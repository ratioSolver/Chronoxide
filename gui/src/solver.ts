export interface SolverOptions {
  url?: string;
}

export namespace solver {
  export class Solver {

    private readonly options: SolverOptions;
    private socket: WebSocket | null = null;
    private readonly flaws: Map<string, Flaw> = new Map();
    private readonly resolvers: Map<string, Resolver> = new Map();
    private current_flaw: Flaw | null = null;
    private current_resolver: Resolver | null = null;
    private readonly connection_listeners: Set<ConnectionListener> = new Set();
    private readonly listeners: Set<SolverListener> = new Set();

    constructor(options: SolverOptions = {}) {
      this.options = {
        url: 'ws://' + window.location.host + '/ws',
        ...options
      };
    }

    connect() {
      if (this.socket)
        this.socket.close();

      console.log('Connecting to Solver at', this.options.url);
      this.socket = new WebSocket(this.options.url!);
      this.socket.onopen = () => {
        console.log('Solver connected');
        for (const listener of this.connection_listeners) listener.connected();
      };
      this.socket.onclose = () => {
        console.log('Solver disconnected');
        for (const listener of this.connection_listeners) listener.disconnected();
      };
      this.socket.onerror = (error) => {
        console.error('Solver connection error', error);
        for (const listener of this.connection_listeners) listener.connection_error(error);
      };
      this.socket.onmessage = (event) => {
        console.trace('Solver message received:', event.data);
        const msg: ServerMessage = JSON.parse(event.data);
        switch (msg.msg_type) {
          case 'status': {
            for (const [id, flaw_msg] of Object.entries(msg.flaws))
              this.flaws.set(id, new Flaw(this, id, flaw_msg.phi, flaw_msg.causes ?? [], flaw_msg.supports ?? [], flaw_msg.status, flaw_msg.cost));
            for (const [id, resolver_msg] of Object.entries(msg.resolvers))
              this.resolvers.set(id, new Resolver(this, id, resolver_msg.rho, resolver_msg.flaw_id, resolver_msg.intrinsic_cost, resolver_msg.sub_flaws ?? [], resolver_msg.status));

            for (const listener of this.listeners) listener.initialized();
            break;
          }
          case 'new-flaw': {
            const flaw = new Flaw(this, msg.id, msg.phi, msg.causes ?? [], msg.supports ?? [], msg.status, msg.cost);
            this.flaws.set(msg.id, flaw);
            for (const listener of this.listeners) listener.new_flaw(flaw);
            break;
          }
          case 'flaw-status-update': {
            const flaw = this.flaws.get(msg.id)!;
            flaw._set_status(msg.status);
            for (const listener of this.listeners) listener.flaw_status_update(flaw);
            break;
          }
          case 'flaw-cost-update': {
            const flaw = this.flaws.get(msg.id)!;
            flaw._set_cost(msg.cost);
            for (const listener of this.listeners) listener.flaw_cost_update(flaw);
            break;
          }
          case 'current-flaw': {
            if (msg.id) {
              this.current_flaw = this.flaws.get(msg.id)!;
              for (const listener of this.listeners) listener.current_flaw(this.current_flaw);
            } else {
              this.current_flaw = null;
              for (const listener of this.listeners) listener.current_flaw(null);
            }
            break;
          }
          case 'new-resolver': {
            const resolver = new Resolver(this, msg.id, msg.rho, msg.flaw_id, msg.intrinsic_cost, msg.sub_flaws ?? [], msg.status);
            this.resolvers.set(msg.id, resolver);
            for (const listener of this.listeners) listener.new_resolver(resolver);
            break;
          }
          case 'resolver-status-update': {
            const resolver = this.resolvers.get(msg.id)!;
            resolver._set_status(msg.status);
            for (const listener of this.listeners) listener.resolver_status_update(resolver);
            break;
          }
          case 'current-resolver': {
            if (msg.id) {
              this.current_resolver = this.resolvers.get(msg.id)!;
              for (const listener of this.listeners) listener.current_resolver(this.current_resolver);
            } else {
              this.current_resolver = null;
              for (const listener of this.listeners) listener.current_resolver(null);
            }
            break;
          }
          case 'new-causal-link': {
            const flaw = this.flaws.get(msg.flaw_id)!;
            const resolver = this.resolvers.get(msg.resolver_id)!;
            flaw._add_support(resolver.get_id());
            resolver._add_sub_flaw(flaw.get_id());
            for (const listener of this.listeners) listener.new_causal_link(flaw, resolver);
            break;
          }
          default:
            console.warn('Received unknown message type from solver:', msg);
        }
      }
    }

    get_flaws(): Flaw[] { return Array.from(this.flaws.values()); }
    get_flaw(id: string): Flaw | undefined { return this.flaws.get(id); }
    get_resolvers(): Resolver[] { return Array.from(this.resolvers.values()); }
    get_resolver(id: string): Resolver | undefined { return this.resolvers.get(id); }

    get_current_flaw(): Flaw | null { return this.current_flaw; }
    get_current_resolver(): Resolver | null { return this.current_resolver; }

    add_connection_listener(listener: ConnectionListener) { this.connection_listeners.add(listener); }
    remove_connection_listener(listener: ConnectionListener) { this.connection_listeners.delete(listener); }

    add_listener(listener: SolverListener) { this.listeners.add(listener); }
    remove_listener(listener: SolverListener) { this.listeners.delete(listener); }
  }

  export interface ConnectionListener {
    connected(): void;
    disconnected(): void;
    connection_error(error: Event): void;
  }

  export interface SolverListener {
    initialized(): void;
    new_flaw(flaw: Flaw): void;
    flaw_status_update(flaw: Flaw): void;
    flaw_cost_update(flaw: Flaw): void;
    current_flaw(flaw: Flaw | null): void;
    new_resolver(resolver: Resolver): void;
    resolver_status_update(resolver: Resolver): void;
    current_resolver(resolver: Resolver | null): void;
    new_causal_link(flaw: Flaw, resolver: Resolver): void;
  }

  export class Flaw {
    private readonly solver: Solver;
    private readonly id: string;
    private readonly phi: string;
    private readonly causes: string[];
    private supports: string[];
    private status: Status;
    private cost?: number;

    constructor(solver: Solver, id: string, phi: string, causes: string[], supports: string[], status: Status, cost?: number) {
      this.solver = solver;
      this.id = id;
      this.phi = phi;
      this.causes = causes;
      this.supports = supports;
      this.status = status;
      this.cost = cost;
      for (const support_id of supports) {
        solver.get_resolver(support_id)!._add_sub_flaw(id);
      }
    }

    get_solver(): Solver { return this.solver; }
    get_id(): string { return this.id; }
    get_phi(): string { return this.phi; }
    get_causes(): string[] { return this.causes; }
    get_supports(): string[] { return this.supports; }
    _add_support(support_id: string) { this.supports.push(support_id); }
    get_status(): Status { return this.status; }
    _set_status(status: Status) { this.status = status; }
    get_cost(): number { return this.cost ?? Infinity; }
    _set_cost(cost?: number) { this.cost = cost; }
  }

  export class Resolver {
    private readonly solver: Solver;
    private readonly id: string;
    private readonly rho: string;
    private readonly flaw: string;
    private readonly intrinsic_cost: number;
    private sub_flaws: string[];
    private status: Status;

    constructor(solver: Solver, id: string, rho: string, flaw: string, intrinsic_cost: number, sub_flaws: string[], status: Status) {
      this.solver = solver;
      this.id = id;
      this.rho = rho;
      this.flaw = flaw;
      this.intrinsic_cost = intrinsic_cost;
      this.sub_flaws = sub_flaws;
      this.status = status;
    }

    get_solver(): Solver { return this.solver; }
    get_id(): string { return this.id; }
    get_rho(): string { return this.rho; }
    get_flaw(): string { return this.flaw; }
    get_sub_flaws(): string[] { return this.sub_flaws; }
    _add_sub_flaw(sub_flaw_id: string) { this.sub_flaws.push(sub_flaw_id); }
    get_intrinsic_cost(): number { return this.intrinsic_cost; }
    get_cost(): number {
      const req_costs = this.sub_flaws.map(req_id => this.solver.get_flaw(req_id)!.get_cost());
      const max_req_cost = req_costs.length > 0 ? Math.max(...req_costs) : 0;
      return this.get_intrinsic_cost() + max_req_cost;
    }
    get_status(): Status { return this.status; }
    _set_status(status: Status) { this.status = status; }
  }

  type SolverMessage = { flaws: Record<string, PartialFlawMessage>, resolvers: Record<string, PartialResolverMessage> };
  type PartialFlawMessage = { phi: string, causes?: string[], supports?: string[], cost?: number, status: Status };
  type FlawMessage = ({ id: string } & PartialFlawMessage);
  type PartialResolverMessage = { rho: string, flaw_id: string, sub_flaws?: string[], intrinsic_cost: number, status: Status };
  type ResolverMessage = ({ id: string } & PartialResolverMessage);
  export type Status = true | false | null;

  type ServerMessage =
    | ({ msg_type: 'status' } & SolverMessage)
    | ({ msg_type: 'new-flaw' } & FlawMessage)
    | ({ msg_type: 'flaw-status-update' } & { id: string, status: Status })
    | ({ msg_type: 'flaw-cost-update' } & { id: string, cost?: number })
    | ({ msg_type: 'current-flaw' } & { id: string | undefined })
    | ({ msg_type: 'new-resolver' } & ResolverMessage)
    | ({ msg_type: 'resolver-status-update' } & { id: string, status: Status })
    | ({ msg_type: 'current-resolver' } & { id: string | undefined })
    | ({ msg_type: 'new-causal-link' } & { flaw_id: string, resolver_id: string })
}