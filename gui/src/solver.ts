export interface SolverOptions {
  url?: string;
}

export namespace solver {
  export class Solver {

    private readonly options: SolverOptions;
    private socket: WebSocket | null = null;
    private readonly objects: Map<string, Item> = new Map();
    private readonly atoms: Map<string, Atom> = new Map();
    private readonly flaws: Map<string, Flaw> = new Map();
    private readonly resolvers: Map<string, Resolver> = new Map();
    private current_flaw: Flaw | null = null;
    private current_resolver: Resolver | null = null;
    private readonly agenda: Set<Flaw> = new Set();
    private timelines: Map<string, Timeline> = new Map();
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
          case 'state-update': {
            for (const [id, item_msg] of Object.entries(msg.objects))
              this.objects.set(id, new Item(id, item_msg.class, item_msg.env));
            for (const [id, atom_msg] of Object.entries(msg.atoms))
              this.atoms.set(id, new Atom(id, atom_msg.fact, atom_msg.predicate, atom_msg.env));
            for (const [id, flaw_msg] of Object.entries(msg.flaws)) {
              const { phi, causes, required_by, status, cost, ...data } = flaw_msg;
              this.flaws.set(id, new Flaw(this, id, phi, causes ?? [], required_by ?? [], status, cost, data));
            }
            for (const [id, resolver_msg] of Object.entries(msg.resolvers)) {
              const { rho, flaw_id, intrinsic_cost, preconditions, status, ...data } = resolver_msg;
              this.resolvers.set(id, new Resolver(this, id, rho, flaw_id, intrinsic_cost, preconditions ?? [], status, data));
            } for (const [id, timeline] of Object.entries(msg.timelines))
              this.timelines.set(id, timeline);
            this.listeners.forEach(listener => listener.state_update());
            break;
          }
          case 'new-object': {
            const item = new Item(msg.id, msg.class, msg.env);
            this.objects.set(msg.id, item);
            break;
          }
          case 'new-atom': {
            const atom = new Atom(msg.id, msg.fact, msg.predicate, msg.env);
            this.atoms.set(msg.id, atom);
            break;
          }
          case 'new-flaw': {
            const { msg_type, id, phi, causes, required_by, status, cost, ...data } = msg;
            const flaw = new Flaw(this, id, phi, causes ?? [], required_by ?? [], status, cost, data);
            this.flaws.set(id, flaw);
            this.listeners.forEach(listener => listener.new_flaw(flaw));
            break;
          }
          case 'flaw-status-update': {
            const flaw = this.flaws.get(msg.id)!;
            flaw._set_status(msg.status);
            this.listeners.forEach(listener => listener.flaw_status_update(flaw));
            break;
          }
          case 'flaw-cost-update': {
            const flaw = this.flaws.get(msg.id)!;
            flaw._set_cost(msg.cost);
            this.listeners.forEach(listener => listener.flaw_cost_update(flaw));
            break;
          }
          case 'current-flaw': {
            if (msg.id) {
              this.current_flaw = this.flaws.get(msg.id)!;
              this.listeners.forEach(listener => listener.current_flaw(this.current_flaw));
            } else {
              this.current_flaw = null;
              this.listeners.forEach(listener => listener.current_flaw(null));
            }
            break;
          }
          case 'new-resolver': {
            const { msg_type, id, rho, flaw_id, intrinsic_cost, preconditions, status, ...data } = msg;
            const resolver = new Resolver(this, id, rho, flaw_id, intrinsic_cost, preconditions ?? [], status, data);
            this.resolvers.set(id, resolver);
            this.listeners.forEach(listener => listener.new_resolver(resolver));
            break;
          }
          case 'resolver-status-update': {
            const resolver = this.resolvers.get(msg.id)!;
            resolver._set_status(msg.status);
            this.listeners.forEach(listener => listener.resolver_status_update(resolver));
            break;
          }
          case 'current-resolver': {
            if (msg.id) {
              this.current_resolver = this.resolvers.get(msg.id)!;
              this.listeners.forEach(listener => listener.current_resolver(this.current_resolver));
            } else {
              this.current_resolver = null;
              this.listeners.forEach(listener => listener.current_resolver(null));
            }
            break;
          }
          case 'new-causal-link': {
            const flaw = this.flaws.get(msg.flaw_id)!;
            const resolver = this.resolvers.get(msg.resolver_id)!;
            flaw._add_required_by(resolver.get_id());
            resolver._add_precondition(flaw.get_id());
            this.listeners.forEach(listener => listener.new_causal_link(flaw, resolver));
            break;
          }
          case 'to-solve-flaw': {
            const flaw = this.flaws.get(msg.flaw_id)!;
            if (!this.agenda.has(flaw)) {
              this.agenda.add(flaw);
              this.listeners.forEach(listener => listener.to_solve_flaw(flaw));
            }
            break;
          }
          case 'solved-flaw': {
            const flaw = this.flaws.get(msg.flaw_id)!;
            if (this.agenda.delete(flaw))
              this.listeners.forEach(listener => listener.solved_flaw(flaw));
            break;
          }
          default:
            console.warn('Received unknown message type from solver:', msg);
        }
      }
    }

    get_objects(): ReadonlyArray<Item> { return Array.from(this.objects.values()); }
    get_object(id: string): Readonly<Item> | undefined { return this.objects.get(id); }
    get_atoms(): ReadonlyArray<Atom> { return Array.from(this.atoms.values()); }
    get_atom(id: string): Readonly<Atom> | undefined { return this.atoms.get(id); }
    get_flaws(): ReadonlyArray<Flaw> { return Array.from(this.flaws.values()); }
    get_flaw(id: string): Readonly<Flaw> | undefined { return this.flaws.get(id); }
    get_resolvers(): ReadonlyArray<Resolver> { return Array.from(this.resolvers.values()); }
    get_resolver(id: string): Readonly<Resolver> | undefined { return this.resolvers.get(id); }

    get_current_flaw(): Readonly<Flaw> | null { return this.current_flaw; }
    get_current_resolver(): Readonly<Resolver> | null { return this.current_resolver; }
    get_agenda(): ReadonlySet<Flaw> { return this.agenda; }

    get_timelines(): ReadonlyMap<string, Timeline> { return this.timelines; }

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
    new_flaw(flaw: Flaw): void;
    flaw_status_update(flaw: Flaw): void;
    flaw_cost_update(flaw: Flaw): void;
    current_flaw(flaw: Flaw | null): void;
    new_resolver(resolver: Resolver): void;
    resolver_status_update(resolver: Resolver): void;
    current_resolver(resolver: Resolver | null): void;
    new_causal_link(flaw: Flaw, resolver: Resolver): void;
    to_solve_flaw(flaw: Flaw): void;
    solved_flaw(flaw: Flaw): void;
    state_update(): void;
  }

  export class Item {
    private readonly id: string;
    private readonly cls: string;
    private readonly env: Record<string, Value>;

    constructor(id: string, cls: string, env: Record<string, Value>) {
      this.id = id;
      this.cls = cls;
      this.env = env;
    }

    get_id(): string { return this.id; }
    get_class(): string { return this.cls; }
    get_env(): Record<string, Value> { return this.env; }
    to_string(): string {
      const args = Object.entries(this.env).map(([k, v]) => `${k}: ${value_to_string(v)}`).join(', ');
      return `${this.cls}(${args})`;
    }
  }

  export class Atom {
    private readonly id: string;
    private readonly fact: boolean;
    private readonly predicate: string;
    private readonly env: Record<string, Value>;

    constructor(id: string, fact: boolean, predicate: string, env: Record<string, Value>) {
      this.id = id;
      this.fact = fact;
      this.predicate = predicate;
      this.env = env;
    }

    get_id(): string { return this.id; }
    is_fact(): boolean { return this.fact; }
    get_predicate(): string { return this.predicate; }
    get_env(): Record<string, Value> { return this.env; }
    to_string(): string {
      const args = Object.entries(this.env).map(([k, v]) => `${k}: ${value_to_string(v)}`).join(', ');
      return `${this.predicate}(${args})`;
    }
  }

  export class Flaw {
    private readonly solver: Solver;
    private readonly id: string;
    private readonly phi: string;
    private readonly causes: string[];
    private required_by: string[];
    private status: Status;
    private cost?: number;
    private readonly data: Record<string, unknown>;

    constructor(solver: Solver, id: string, phi: string, causes: string[], required_by: string[], status: Status, cost?: number, data?: Record<string, unknown>) {
      this.solver = solver;
      this.id = id;
      this.phi = phi;
      this.causes = causes;
      this.required_by = required_by;
      this.status = status;
      this.cost = cost;
      this.data = data ?? {};
      for (const support_id of required_by) {
        solver.get_resolver(support_id)?._add_precondition(id);
      }
    }

    get_solver(): Solver { return this.solver; }
    get_id(): string { return this.id; }
    get_phi(): string { return this.phi; }
    get_causes(): string[] { return this.causes; }
    get_required_by(): string[] { return this.required_by; }
    _add_required_by(res_id: string) { if (!this.required_by.includes(res_id)) this.required_by.push(res_id); }
    get_status(): Status { return this.status; }
    _set_status(status: Status) { this.status = status; }
    get_cost(): number { return this.cost ?? Infinity; }
    _set_cost(cost?: number) { this.cost = cost; }
    get_data(): Record<string, unknown> { return this.data; }
  }

  export class Resolver {
    private readonly solver: Solver;
    private readonly id: string;
    private readonly rho: string;
    private readonly flaw: string;
    private readonly intrinsic_cost: number;
    private preconditions: string[];
    private status: Status;
    private readonly data: Record<string, unknown>;

    constructor(solver: Solver, id: string, rho: string, flaw: string, intrinsic_cost: number, preconditions: string[], status: Status, data?: Record<string, unknown>) {
      this.solver = solver;
      this.id = id;
      this.rho = rho;
      this.flaw = flaw;
      this.intrinsic_cost = intrinsic_cost;
      this.preconditions = preconditions;
      this.status = status;
      this.data = data ?? {};
      for (const pre_id of preconditions) {
        solver.get_flaw(pre_id)?._add_required_by(id);
      }
    }

    get_solver(): Solver { return this.solver; }
    get_id(): string { return this.id; }
    get_rho(): string { return this.rho; }
    get_flaw(): string { return this.flaw; }
    get_preconditions(): string[] { return this.preconditions; }
    _add_precondition(flaw_id: string) { if (!this.preconditions.includes(flaw_id)) this.preconditions.push(flaw_id); }
    get_intrinsic_cost(): number { return this.intrinsic_cost; }
    get_cost(): number {
      const req_costs = this.preconditions.map(req_id => this.solver.get_flaw(req_id)!.get_cost());
      const max_req_cost = req_costs.length > 0 ? Math.max(...req_costs) : 0;
      return this.get_intrinsic_cost() + max_req_cost;
    }
    get_status(): Status { return this.status; }
    _set_status(status: Status) { this.status = status; }
    get_data(): Record<string, unknown> { return this.data; }
  }

  export function value_to_string(val: Value): string {
    if (typeof val === 'object' && val !== null) {
      if ('type' in val && 'id' in val)
        return val.id;
      else if ('num' in val && 'den' in val) {
        const numVal = val.num / val.den;
        if (val.inf) {
          const infVal = val.inf.num / val.inf.den;
          if (infVal > 0) {
            return `${numVal} +${infVal}ϵ`;
          } else if (infVal < 0) {
            return `${numVal} -${-infVal}ϵ`;
          }
        }
        return String(numVal);
      }
    } else if (typeof val === 'string')
      return `"${val}"`;
    else if (typeof val === 'boolean')
      return String(val);
    throw new Error('Unknown value type');
  }

  export type StateVariableInterval = { start: InfRational; end: InfRational; atoms: string[]; };
  export type StateVariableTimeline = { type: 'StateVariable'; intervals: StateVariableInterval[]; };
  export type ReusableResourceInterval = { start: InfRational; end: InfRational; amount: InfRational; };
  export type ReusableResourceTimeline = { type: 'ReusableResource'; capacity: InfRational; intervals: ReusableResourceInterval[]; };
  export type Timeline = StateVariableTimeline | ReusableResourceTimeline;
  export type Value = InfRational | string | boolean | { type: 'object_ref' | 'atom_ref'; id: string; };
  type ObjectMessage = { class: string; env: Record<string, Value>; };
  type AtomMessage = { predicate: string; fact: boolean, env: Record<string, Value>; };
  type SolverMessage = { objects: Record<string, ObjectMessage>, atoms: Record<string, AtomMessage>, flaws: Record<string, FlawMessage>, resolvers: Record<string, ResolverMessage>, timelines: Record<string, Timeline> };
  type FlawMessage = { phi: string, causes?: string[], required_by?: string[], cost?: number, status: Status } & Record<string, unknown>;
  type ResolverMessage = { rho: string, flaw_id: string, preconditions?: string[], intrinsic_cost: number, status: Status } & Record<string, unknown>;
  export type Rational = { num: number, den: number };
  export type InfRational = Rational & { inf?: Rational };
  export type Status = true | false | null;

  type ServerMessage =
    | ({ msg_type: 'state-update' } & SolverMessage)
    | ({ msg_type: 'new-object' } & { id: string } & ObjectMessage)
    | ({ msg_type: 'new-atom' } & { id: string } & AtomMessage)
    | ({ msg_type: 'new-flaw' } & { id: string } & FlawMessage)
    | ({ msg_type: 'flaw-status-update' } & { id: string, status: Status })
    | ({ msg_type: 'flaw-cost-update' } & { id: string, cost?: number })
    | ({ msg_type: 'current-flaw' } & { id: string | undefined })
    | ({ msg_type: 'new-resolver' } & { id: string } & ResolverMessage)
    | ({ msg_type: 'resolver-status-update' } & { id: string, status: Status })
    | ({ msg_type: 'current-resolver' } & { id: string | undefined })
    | ({ msg_type: 'new-causal-link' } & { flaw_id: string, resolver_id: string })
    | ({ msg_type: 'to-solve-flaw' } & { flaw_id: string })
    | ({ msg_type: 'solved-flaw' } & { flaw_id: string })
    | ({ msg_type: 'state-update' } & SolverMessage);
}