import { h, VNode } from "snabbdom";
import { solver } from "../solver";
import * as echarts from 'echarts/core';
import { GraphChart } from "echarts/charts";
import { CanvasRenderer } from 'echarts/renderers';

echarts.use([GraphChart, CanvasRenderer]);

export function causal_graph(slv: solver.Solver): VNode {
  let chart: echarts.ECharts | undefined;

  const get_option = (): echarts.EChartsCoreOption => {
    const flaws = slv.get_flaws();
    const resolvers = slv.get_resolvers();

    const data = [
      ...flaws.map((flaw) => ({
        id: flaw.get_id(),
        name: flaw.get_phi(),
        symbol: 'circle',
      })),
      ...resolvers.map((resolver) => ({
        id: resolver.get_id(),
        name: resolver.get_rho(),
        symbol: 'rect',
      })),
    ];

    const links = resolvers.map((resolver) => ({
      source: resolver.get_id(),
      target: resolver.get_flaw().get_id(),
    }));

    return {
      series: [
        {
          type: 'graph',
          layout: 'force',
          draggable: true,
          data,
          links,
          roam: true,
          label: {
            show: true,
            position: 'right'
          },
          force: {
            repulsion: 100,
            edgeLength: 50,
            gravity: 0.1
          }
        }
      ]
    };
  };

  const solver_listener = {
    initialized: () => { if (chart) chart.setOption(get_option()); },
    new_flaw: (_flaw: solver.Flaw) => { if (chart) chart.setOption(get_option()); },
    new_resolver: (_resolver: solver.Resolver) => { if (chart) chart.setOption(get_option()); },

    connected: () => { },
    disconnected: () => { },
    connection_error: (error: Event) => console.error('Solver connection error', error),
  };

  let resize_handler: () => void;

  return h('div#causal_graph.flex-grow-1', {
    hook: {
      insert: (vnode) => {
        chart = echarts.init(vnode.elm as HTMLDivElement);
        chart.setOption(get_option());

        resize_handler = () => chart?.resize();
        window.addEventListener('resize', resize_handler);

        slv.add_listener(solver_listener);
      },
      destroy: () => {
        window.removeEventListener('resize', resize_handler);
        slv.remove_listener(solver_listener);
        if (chart) {
          chart.dispose();
          chart = undefined;
        }
      }
    }
  });
}