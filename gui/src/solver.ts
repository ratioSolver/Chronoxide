export interface SolverOptions {
  url?: string;
}

export namespace solver {
  export class Solver {

    private readonly options: SolverOptions;
    private socket: WebSocket | null = null;
    private readonly flaws: Map<string, Flaw> = new Map();
    private readonly resolvers: Map<string, Resolver> = new Map();
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
              this.flaws.set(id, new Flaw(id, flaw_msg.phi));
            for (const [id, resolver_msg] of Object.entries(msg.resolvers))
              this.resolvers.set(id, new Resolver(id, resolver_msg.rho, this.flaws.get(resolver_msg.flaw)!));

            for (const listener of this.listeners) listener.initialized();
            break;
          }
          case 'new-flaw': {
            const flaw = new Flaw(msg.id, msg.phi);
            this.flaws.set(msg.id, flaw);
            for (const listener of this.listeners) listener.new_flaw(flaw);
            break;
          }
          case 'new-resolver': {
            const resolver = new Resolver(msg.id, msg.rho, this.flaws.get(msg.flaw)!);
            this.resolvers.set(msg.id, resolver);
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
    new_resolver(resolver: Resolver): void;
  }

  export class Flaw {
    private readonly id: string;
    private readonly phi: string;

    constructor(id: string, phi: string) {
      this.id = id;
      this.phi = phi;
    }

    get_id(): string { return this.id; }
    get_phi(): string { return this.phi; }
  }

  export class Resolver {
    private readonly id: string;
    private readonly rho: string;
    private readonly flaw: Flaw;

    constructor(id: string, rho: string, flaw: Flaw) {
      this.id = id;
      this.rho = rho;
      this.flaw = flaw;
    }

    get_id(): string { return this.id; }
    get_rho(): string { return this.rho; }
    get_flaw(): Flaw { return this.flaw; }
  }

  type SolverMessage = { flaws: Record<string, PartialFlawMessage>, resolvers: Record<string, PartialResolverMessage> };
  type PartialFlawMessage = { phi: string };
  type FlawMessage = ({ id: string } & PartialFlawMessage);
  type PartialResolverMessage = { rho: string, flaw: string };
  type ResolverMessage = ({ id: string } & PartialResolverMessage);

  type ServerMessage =
    | ({ msg_type: 'status' } & SolverMessage)
    | ({ msg_type: 'new-flaw' } & FlawMessage)
    | ({ msg_type: 'new-resolver' } & ResolverMessage);
}