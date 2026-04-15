import { h, VNode } from "snabbdom";
import { App, flick, Navbar, NavbarItem, NavbarList, OffcanvasBrand } from "@ratiosolver/flick";
import { solver } from "../solver";
import { causal_graph } from "./causal_graph";
import { timelines } from "./timelines";

const app_listener = {
  initialized: () => flick.redraw(),
  new_flaw: (_flaw: solver.Flaw) => { },
  flaw_cost_update: (_flaw: solver.Flaw) => { },
  new_resolver: (_resolver: solver.Resolver) => { },

  connected: () => { },
  disconnected: () => { },
  connection_error: (error: Event) => console.error('CoCo connection error', error),
};

const landing_page = () => h('div.container.mt-5', [
  h('div.text-center.mb-5', [
    h('h1.display-4', 'Chronoxide'),
    h('p.lead', 'An Integrated Logic and Constraint based solver')
  ]),
  h('div.row.justify-content-center', [
    h('div.col-lg-8', [
      h('p', 'Chronoxide is an Integrated Logic and Constraint based solver written in Rust which takes inspiration from both Logic Programming (LP) and Constraint Programming (CP).'),
      h('hr.my-4'),
      h('h4', 'Features'),
      h('ul.list-group.list-group-flush', [
        h('li.list-group-item', [h('strong', 'Integrated LP + CP'), ': Combines logic programming and constraint programming in a single solver.']),
        h('li.list-group-item', [h('strong', 'Constraint Solving Engine'), ': Supports boolean, arithmetic, and symbolic reasoning over shared models.']),
        h('li.list-group-item', [h('strong', 'Rust Core'), ': Built for performance, memory safety, and reliability.']),
        h('li.list-group-item', [h('strong', 'Web Tooling'), ': Provides an Axum-based server and interactive visualization components.']),
      ])
    ])
  ])
]);

flick.ctx.current_page = landing_page;
flick.ctx.page_title = 'Home';

export function SolverApp(slv: solver.Solver): VNode {
  const content = h('div.flex-grow-1.d-flex.flex-column',
    {
      hook: {
        insert: () => {
          slv.add_listener(app_listener);
        },
        destroy: () => {
          slv.remove_listener(app_listener);
        }
      }
    }, [
    (flick.ctx.current_page as () => VNode)()
  ]);

  return App(Navbar(OffcanvasBrand('Chronoxide'), NavbarList([NavbarItem(h('i.fas.fa-home', {
    on: {
      click: () => {
        flick.ctx.current_page = landing_page;
        flick.ctx.page_title = 'Home';
        flick.redraw();
      }
    }
  })),
  NavbarItem(h('i.fas.fa-stream', {
    on: {
      click: () => {
        flick.ctx.current_page = () => timelines(slv);
        flick.ctx.page_title = 'Timelines';
        flick.redraw();
      }
    }
  })),
  NavbarItem(h('i.fas.fa-project-diagram', {
    on: {
      click: () => {
        flick.ctx.current_page = () => causal_graph(slv);
        flick.ctx.page_title = 'Causal graph';
        flick.redraw();
      }
    }
  }))])), content);
}