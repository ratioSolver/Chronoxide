import { h, VNode } from "snabbdom";
import { App, flick, Navbar, NavbarItem, NavbarList, OffcanvasBrand } from "@ratiosolver/flick";
import { solver } from "../solver";
import { causal_graph } from "./causal_graph";

const app_listener = {
  initialized: () => flick.redraw(),
  connection_error: (error: Event) => console.error('CoCo connection error', error),
  connected: () => { },
  disconnected: () => { },
};

const landing_page = () => h('div.container.mt-5', [
  h('div.text-center.mb-5', [
    h('h1.display-4', 'CoCo'),
    h('p.lead', 'Combined Deduction and Abduction Reasoner'),
  ]),
  h('div.row.justify-content-center', [
    h('div.col-lg-8', [
      h('p', 'CoCo is a dual-process inspired cognitive architecture built in Rust. It integrates a rule-based expert system and a timeline-based planner to invoke deductive and abductive reasoning in dynamic environments.'),
      h('hr.my-4'),
      h('h4', 'Features'),
      h('ul.list-group.list-group-flush', [
        h('li.list-group-item', [h('strong', 'Hybrid Reasoning'), ': Unites deductive logic with abductive inference.']),
        h('li.list-group-item', [h('strong', 'Rust Core'), ': Designed for performance, memory safety, and concurrency.']),
        h('li.list-group-item', [h('strong', 'CLIPS Integration'), ': Seamless binding with the C-based CLIPS expert system.']),
        h('li.list-group-item', [h('strong', 'Web Interface'), ': Includes a web server (Axum) and visualization tools.']),
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

  return App(Navbar(OffcanvasBrand('CoCo'), NavbarList([NavbarItem(h('i.fas.fa-home', {
    on: {
      click: () => {
        flick.ctx.current_page = landing_page;
        flick.ctx.page_title = 'Home';
        flick.redraw();
      }
    }
  })),
  NavbarItem(h('i.fas.fa-sitemap', {
    on: {
      click: () => {
        flick.ctx.current_page = () => causal_graph(slv);
        flick.ctx.page_title = 'Causal graph';
        flick.redraw();
      }
    }
  }))])), content);
}