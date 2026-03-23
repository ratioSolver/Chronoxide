import { h, VNode } from "snabbdom";
import { solver } from "../solver";
import * as echarts from 'echarts/core';
import { GraphChart } from "echarts/charts";

echarts.use([GraphChart]);

export function causal_graph(slv: solver.Solver): VNode {
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
    connection_error: (error: Event) => console.error('Solver connection error', error),
    connected: () => { },
    disconnected: () => { },
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