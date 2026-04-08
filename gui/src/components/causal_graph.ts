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
      ...flaws.map((flaw) => {
        return {
          id: String(flaw.get_id()),
          name: flaw.get_phi(),
          symbol: 'circle',
          itemStyle: {
            color: node_color(flaw.get_cost(), flaw.get_status()),
            borderColor: 'black',
            borderType: node_border(flaw.get_status())
          },
        };
      }),
      ...resolvers.map((resolver) => ({
        id: String(resolver.get_id()),
        name: resolver.get_rho(),
        symbol: 'rect',
        itemStyle: {
          borderColor: 'black',
          borderType: node_border(resolver.get_status())
        },
      })),
    ];

    const links = resolvers.map((resolver) => ({
      source: String(resolver.get_id()),
      target: String(resolver.get_flaw().get_id()),
      lineStyle: edge_style(resolver.get_status()),
    }));

    return {
      series: [
        {
          type: 'graph',
          layout: 'force',
          draggable: true,
          data,
          links,
          edgeSymbol: ['none', 'arrow'],
          edgeSymbolSize: 10,
          lineStyle: edge_style('active'),
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

function node_color(cost: number, status: 'active' | 'forbidden' | 'inactive'): string {
  if (!isFinite(cost))
    return '#1f2937';

  if (status === 'forbidden')
    return '#9ca3af';

  // Map [0, ∞) → hue [120, 0] (green → red) using atan normalization
  const t = (2 / Math.PI) * Math.atan(cost);
  const hue = Math.round(120 * (1 - t));
  return `hsl(${hue}, 80%, 45%)`;
}

function node_border(status: 'active' | 'forbidden' | 'inactive'): string {
  switch (status) {
    case 'active':
      return 'solid';
    case 'inactive':
      return 'dashed';
    case 'forbidden':
      return 'dotted';
  }
}

function edge_style(status: 'active' | 'forbidden' | 'inactive') {
  switch (status) {
    case 'active':
      return {
        width: 1.8,
        color: '#1f2937',
        opacity: 0.95,
        type: 'solid'
      };
    case 'inactive':
      return {
        width: 1.5,
        color: '#6b7280',
        opacity: 0.75,
        type: 'dashed'
      };
    case 'forbidden':
      return {
        width: 1.2,
        color: '#9ca3af',
        opacity: 0.6,
        type: 'dotted'
      };
  }
}