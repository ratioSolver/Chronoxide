import { h, VNode } from "snabbdom";
import { solver } from "../solver";
import * as echarts from 'echarts/core';
import { GraphChart } from "echarts/charts";
import { CanvasRenderer } from 'echarts/renderers';

echarts.use([GraphChart, CanvasRenderer]);

export function timelines(slv: solver.Solver): VNode {
  let chart: echarts.ECharts | undefined;

  const get_option = (): echarts.EChartsCoreOption => {
    return {
      series: [
        {
          type: 'graph',
          layout: 'force',
          draggable: true,
          data: [],
          links: [],
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
    initialized: () => { },
    new_flaw: (_flaw: solver.Flaw) => { },
    flaw_cost_update: (_flaw: solver.Flaw) => { },
    new_resolver: (_resolver: solver.Resolver) => { },

    connected: () => { },
    disconnected: () => { },
    connection_error: (error: Event) => console.error('Solver connection error', error),
  };

  let resize_handler: () => void;

  return h('div#timelines.flex-grow-1', {
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