export interface SolverOptions {
  url?: string;
}

export namespace solver {
  export class Solver {

    private readonly options: SolverOptions;
    private socket: WebSocket | null = null;
    private readonly flaws: Map<number, Flaw> = new Map();
    private readonly resolvers: Map<number, Resolver> = new Map();
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
        for (const listener of this.listeners) listener.connected();
      };
      this.socket.onclose = () => {
        console.log('Solver disconnected');
        for (const listener of this.listeners) listener.disconnected();
      };
      this.socket.onerror = (error) => {
        console.error('Solver connection error', error);
        for (const listener of this.listeners) listener.connection_error(error);
      };
      this.socket.onmessage = (event) => {
        console.trace('Solver message received:', event.data);
        const msg: ServerMessage = JSON.parse(event.data);
        switch (msg.msg_type) {
          case 'status': {
            for (const [id, flaw_msg] of Object.entries(msg.flaws))
              this.flaws.set(Number(id), new Flaw(Number(id), flaw_msg.phi, flaw_msg.status, flaw_msg.cost));
            for (const [id, resolver_msg] of Object.entries(msg.resolvers))
              this.resolvers.set(Number(id), new Resolver(Number(id), resolver_msg.rho, this.flaws.get(Number(resolver_msg.flaw))!, resolver_msg.status));

            for (const listener of this.listeners) listener.initialized();
            break;
          }
          case 'new-flaw': {
            const flaw = new Flaw(msg.id, msg.phi, msg.status, msg.cost);
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
          case 'new-resolver': {
            const resolver = new Resolver(msg.id, msg.rho, this.flaws.get(msg.flaw)!, msg.status);
            this.resolvers.set(Number(msg.id), resolver);
            for (const listener of this.listeners) listener.new_resolver(resolver);
            break;
          }
        }
      }
    }

    get_flaws(): Flaw[] { return Array.from(this.flaws.values()); }
    get_resolvers(): Resolver[] { return Array.from(this.resolvers.values()); }

    add_listener(listener: SolverListener) { this.listeners.add(listener); }
    remove_listener(listener: SolverListener) { this.listeners.delete(listener); }
  }

  export interface SolverListener {

    connected(): void;
    disconnected(): void;
    connection_error(error: Event): void;

    initialized(): void;
    new_flaw(flaw: Flaw): void;
    flaw_cost_update(flaw: Flaw): void;
    new_resolver(resolver: Resolver): void;
  }

  export class Flaw {
    private readonly id: number;
    private readonly phi: string;
    private status: Status;
    private cost: Rational;

    constructor(id: number, phi: string, status: Status, cost: Rational) {
      this.id = id;
      this.phi = phi;
      this.status = status;
      this.cost = cost;
    }

    get_id(): number { return this.id; }
    get_phi(): string { return this.phi; }
    get_status(): Status { return this.status; }
    get_cost(): number { return this.cost.den === 0 ? Infinity : this.cost.num / this.cost.den; }
    _set_cost(cost: Rational) { this.cost = cost; }
  }

  export class Resolver {
    private readonly id: number;
    private readonly rho: string;
    private flaw: Flaw;
    private status: Status;

    constructor(id: number, rho: string, flaw: Flaw, status: Status) {
      this.id = id;
      this.rho = rho;
      this.flaw = flaw;
      this.status = status;
    }

    get_id(): number { return this.id; }
    get_rho(): string { return this.rho; }
    get_flaw(): Flaw { return this.flaw; }
    get_status(): Status { return this.status; }
  }

  type SolverMessage = { flaws: Record<string, PartialFlawMessage>, resolvers: Record<string, PartialResolverMessage> };
  type PartialFlawMessage = { phi: string, cost: Rational, status: Status };
  type FlawMessage = ({ id: number } & PartialFlawMessage);
  type PartialResolverMessage = { rho: string, flaw: number, status: Status };
  type ResolverMessage = ({ id: number } & PartialResolverMessage);
  type Rational = { num: number, den: number };
  type Status = 'active' | 'forbidden' | 'inactive';

  type ServerMessage =
    | ({ msg_type: 'status' } & SolverMessage)
    | ({ msg_type: 'new-flaw' } & FlawMessage)
    | ({ msg_type: 'flaw-cost-update' } & { id: number, cost: Rational })
    | ({ msg_type: 'new-resolver' } & ResolverMessage);
}