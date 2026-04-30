import { h, VNode } from "snabbdom";
import { solver } from "../solver";
import * as echarts from 'echarts/core';
import { GraphChart } from "echarts/charts";
import { CanvasRenderer } from 'echarts/renderers';

echarts.use([GraphChart, CanvasRenderer]);

const CURRENT_NODE_COLOR = '#f97316';
const CURRENT_NODE_BORDER_COLOR = '#7c2d12';
const CURRENT_NODE_SHADOW_COLOR = 'rgba(249, 115, 22, 0.7)';

export function causal_graph(slv: solver.Solver): VNode {
  let chart: echarts.ECharts | undefined;

  const get_option = (): echarts.EChartsCoreOption => {
    const flaws = slv.get_flaws();
    const resolvers = slv.get_resolvers();
    const current_flaw = slv.get_current_flaw();
    const current_resolver = slv.get_current_resolver();

    const data = [
      ...flaws.map((flaw) => {
        const is_current = flaw === current_flaw;
        return {
          id: flaw.get_id(),
          name: flaw.get_phi(),
          symbol: 'circle',
          symbolSize: is_current ? 24 : 16,
          itemStyle: {
            color: is_current ? CURRENT_NODE_COLOR : node_color(flaw.get_cost(), flaw.get_status()),
            borderColor: is_current ? CURRENT_NODE_BORDER_COLOR : 'black',
            borderWidth: is_current ? 3 : 1,
            borderType: node_border(flaw.get_status()),
            shadowBlur: is_current ? 16 : 0,
            shadowColor: CURRENT_NODE_SHADOW_COLOR
          },
        };
      }),
      ...resolvers.map((resolver) => {
        const is_current = resolver === current_resolver;
        return {
          id: resolver.get_id(),
          name: resolver.get_rho(),
          symbol: 'rect',
          symbolSize: is_current ? 24 : 16,
          itemStyle: {
            color: is_current ? CURRENT_NODE_COLOR : node_color(resolver.get_cost(), resolver.get_status()),
            borderColor: is_current ? CURRENT_NODE_BORDER_COLOR : 'black',
            borderWidth: is_current ? 3 : 1,
            borderType: node_border(resolver.get_status()),
            shadowBlur: is_current ? 16 : 0,
            shadowColor: CURRENT_NODE_SHADOW_COLOR
          },
        };
      }),
    ];

    const links = resolvers.map((resolver) => ({
      source: resolver.get_id(),
      target: resolver.get_flaw(),
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
    flaw_cost_update: (_flaw: solver.Flaw | null) => { if (chart) chart.setOption(get_option()); },
    current_flaw: (_flaw: solver.Flaw) => { if (chart) chart.setOption(get_option()); },
    new_resolver: (_resolver: solver.Resolver) => { if (chart) chart.setOption(get_option()); },
    current_resolver: (_resolver: solver.Resolver | null) => { if (chart) chart.setOption(get_option()); },
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

function node_color(cost: number, status: solver.Status): string {
  if (!isFinite(cost))
    return '#1f2937';

  if (status === false)
    return '#9ca3af';

  // Map [0, ∞) → hue [120, 0] (green → red) using atan normalization
  const t = (2 / Math.PI) * Math.atan(cost);
  const hue = Math.round(120 * (1 - t));
  return `hsl(${hue}, 80%, 45%)`;
}

function node_border(status: solver.Status): string {
  switch (status) {
    case true:
      return 'solid';
    case null:
      return 'dashed';
    case false:
      return 'dotted';
  }
}

function edge_style(status: solver.Status) {
  switch (status) {
    case true:
      return {
        width: 1.8,
        color: '#1f2937',
        opacity: 0.95,
        type: 'solid'
      };
    case null:
      return {
        width: 1.5,
        color: '#6b7280',
        opacity: 0.75,
        type: 'dashed'
      };
    case false:
      return {
        width: 1.2,
        color: '#9ca3af',
        opacity: 0.6,
        type: 'dotted'
      };
  }
}