import { flick } from '@ratiosolver/flick';
import { solver } from '../src/solver';
import { SolverApp } from '../src/components/app';
import '@fortawesome/fontawesome-free/css/all.css';

const cc = new solver.Solver({ url: 'ws://localhost:3000/ws' });

flick.mount(() => SolverApp(cc));

cc.connect();