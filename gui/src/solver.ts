export interface SolverOptions {
  url?: string;
}

export namespace solver {
  export class Solver {

    private readonly options: SolverOptions;
    private socket: WebSocket | null = null;
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
            for (const listener of this.listeners) listener.initialized();
            break;
          }
        }
      }
    }

    add_listener(listener: SolverListener) { this.listeners.add(listener); }
    remove_listener(listener: SolverListener) { this.listeners.delete(listener); }
  }

  export interface SolverListener {

    connected(): void;
    disconnected(): void;
    connection_error(error: Event): void;

    initialized(): void;
  }

  type SolverMessage = {};

  type ServerMessage =
    | ({ msg_type: 'status' } & SolverMessage);
}