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
              this.flaws.set(id, new Flaw(this, id, flaw_msg.phi, flaw_msg.causes, flaw_msg.supports, flaw_msg.status, flaw_msg.cost));
            for (const [id, resolver_msg] of Object.entries(msg.resolvers))
              this.resolvers.set(id, new Resolver(this, id, resolver_msg.rho, resolver_msg.flaw, resolver_msg.intrinsic_cost, resolver_msg.requirements, resolver_msg.status));

            for (const listener of this.listeners) listener.initialized();
            break;
          }
          case 'new-flaw': {
            const flaw = new Flaw(this, msg.id, msg.phi, msg.causes, msg.supports, msg.status, msg.cost);
            this.flaws.set(msg.id, flaw);
            for (const listener of this.listeners) listener.new_flaw(flaw);
            break;
          }
          case 'flaw-cost-update': {
            const flaw = this.flaws.get(msg.id);
            if (flaw) {
              flaw._set_cost(msg.cost);
              for (const listener of this.listeners) listener.flaw_cost_update(flaw);
            } else
              console.warn(`Received cost update for unknown flaw with id ${msg.id}`);
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
            const resolver = new Resolver(this, msg.id, msg.rho, msg.flaw, msg.intrinsic_cost, msg.requirements, msg.status);
            this.resolvers.set(msg.id, resolver);
            for (const listener of this.listeners) listener.new_resolver(resolver);
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
    flaw_cost_update(flaw: Flaw): void;
    current_flaw(flaw: Flaw | null): void;
    new_resolver(resolver: Resolver): void;
    current_resolver(resolver: Resolver | null): void;
  }

  export class Flaw {
    private readonly solver: Solver;
    private readonly id: string;
    private readonly phi: number;
    private readonly causes: string[];
    private supports: string[];
    private status: Status;
    private cost: Rational;

    constructor(solver: Solver, id: string, phi: number, causes: string[], supports: string[], status: Status, cost: Rational) {
      this.solver = solver;
      this.id = id;
      this.phi = phi;
      this.causes = causes;
      this.supports = supports;
      this.status = status;
      this.cost = cost;
    }

    get_solver(): Solver { return this.solver; }
    get_id(): string { return this.id; }
    get_phi(): number { return this.phi; }
    get_causes(): string[] { return this.causes; }
    get_supports(): string[] { return this.supports; }
    get_status(): Status { return this.status; }
    get_cost(): number { return this.cost.den === 0 ? Infinity : this.cost.num / this.cost.den; }
    _set_cost(cost: Rational) { this.cost = cost; }
  }

  export class Resolver {
    private readonly solver: Solver;
    private readonly id: string;
    private readonly rho: number;
    private readonly flaw: string;
    private readonly intrinsic_cost: Rational;
    private requirements: string[];
    private status: Status;

    constructor(solver: Solver, id: string, rho: number, flaw: string, intrinsic_cost: Rational, requirements: string[], status: Status) {
      this.solver = solver;
      this.id = id;
      this.rho = rho;
      this.flaw = flaw;
      this.intrinsic_cost = intrinsic_cost;
      this.requirements = requirements;
      this.status = status;
    }

    get_solver(): Solver { return this.solver; }
    get_id(): string { return this.id; }
    get_rho(): number { return this.rho; }
    get_flaw(): string { return this.flaw; }
    get_requirements(): string[] { return this.requirements; }
    get_intrinsic_cost(): number { return this.intrinsic_cost.den === 0 ? Infinity : this.intrinsic_cost.num / this.intrinsic_cost.den; }
    get_cost(): number {
      const req_costs = this.requirements.map(req_id => this.solver.get_flaw(req_id)!.get_cost());
      const max_req_cost = req_costs.length > 0 ? Math.max(...req_costs) : 0;
      return this.get_intrinsic_cost() + max_req_cost;
    }
    get_status(): Status { return this.status; }
  }

  type SolverMessage = { flaws: Record<string, PartialFlawMessage>, resolvers: Record<string, PartialResolverMessage> };
  type PartialFlawMessage = { phi: number, causes: string[], supports: string[], cost: Rational, status: Status };
  type FlawMessage = ({ id: string } & PartialFlawMessage);
  type PartialResolverMessage = { rho: number, flaw: string, requirements: string[], intrinsic_cost: Rational, status: Status };
  type ResolverMessage = ({ id: string } & PartialResolverMessage);
  type Rational = { num: number, den: number };
  export type Status = true | false | null;

  type ServerMessage =
    | ({ msg_type: 'status' } & SolverMessage)
    | ({ msg_type: 'new-flaw' } & FlawMessage)
    | ({ msg_type: 'flaw-status-update' } & { id: string, status: Status })
    | ({ msg_type: 'flaw-cost-update' } & { id: string, cost: Rational })
    | ({ msg_type: 'current-flaw' } & { id: string | undefined })
    | ({ msg_type: 'new-resolver' } & ResolverMessage)
    | ({ msg_type: 'resolver-status-update' } & { id: string, status: Status })
    | ({ msg_type: 'current-resolver' } & { id: string | undefined });
}