import { h, VNode } from "snabbdom";
import { solver } from "../solver";
import * as echarts from 'echarts/core';
import { CustomChart } from "echarts/charts";
import { CanvasRenderer } from 'echarts/renderers';
import { GridComponent, TooltipComponent, DataZoomComponent, TitleComponent } from 'echarts/components';

echarts.use([CustomChart, CanvasRenderer, GridComponent, TooltipComponent, DataZoomComponent, TitleComponent]);

export function timelines(slv: solver.Solver): VNode {
  let chart: echarts.ECharts | undefined;

  const get_option = (): echarts.EChartsCoreOption => {
    const categories: string[] = [];
    const data: any[] = [];

    let yIndex = 0;
    for (const [objId, timeline] of slv.get_timelines()) {
      categories.push(`${objId}`);

      switch (timeline.type) {
        case 'StateVariable':
          for (const interval of timeline.intervals) {
            const start = interval.start.num / interval.start.den;
            const end = interval.end.num / interval.end.den;

            data.push({
              name: `Atoms: ${interval.atoms.join(', ')}`,
              value: [
                yIndex,
                start,
                end,
                interval.atoms
              ],
              itemStyle: {
                color: '#5b8ff9',
                borderWidth: 1,
                borderColor: '#1e3a8a'
              }
            });
          }
          break;
        case 'ReusableResource': {
          const capacity = timeline.capacity.num / timeline.capacity.den;
          for (const interval of timeline.intervals) {
            const start = interval.start.num / interval.start.den;
            const end = interval.end.num / interval.end.den;
            const amount = interval.amount.num / interval.amount.den;

            const fillRatio = amount / capacity;

            data.push({
              name: `Amount: ${amount}`,
              value: [
                yIndex,
                start,
                end,
                fillRatio
              ],
              itemStyle: {
                color: amount > capacity ? '#ef4444' : '#10b981',
                borderWidth: 1,
                borderColor: '#047857'
              }
            });
          }
          break;
        }
      }

      yIndex++;
    }

    return {
      tooltip: {
        formatter: function (params: any) {
          const start = params.value[1];
          const end = params.value[2];
          const atoms = params.value[3].join(', ');
          return `<strong>${params.name}</strong><br/>Start: ${start}<br/>End: ${end}<br/>Atoms: ${atoms}`;
        }
      },
      dataZoom: [
        { type: 'slider', filterMode: 'weakFilter', showDataShadow: false, bottom: 20 },
        { type: 'inside', filterMode: 'weakFilter' }
      ],
      grid: {
        top: 30, right: 30, bottom: 70, left: 100
      },
      xAxis: {
        type: 'value',
        scale: true
      },
      yAxis: {
        type: 'category',
        data: categories
      },
      series: [
        {
          type: 'custom',
          renderItem: renderGanttItem,
          encode: {
            x: [1, 2],
            y: 0
          },
          data: data
        }
      ]
    };
  };

  const renderGanttItem = (params: any, api: any) => {
    const categoryIndex = api.value(0);
    const startCoord = api.coord([api.value(1), categoryIndex]);
    const endCoord = api.coord([api.value(2), categoryIndex]);

    const height = api.size([0, 1])[1] * 0.6;

    const rectShape = echarts.graphic.clipRectByRect({
      x: startCoord[0],
      y: startCoord[1] - height / 2,
      width: Math.max(endCoord[0] - startCoord[0], 2),
      height: height
    }, {
      x: params.coordSys.x,
      y: params.coordSys.y,
      width: params.coordSys.width,
      height: params.coordSys.height
    });

    return rectShape && {
      type: 'rect',
      transition: ['shape'],
      shape: rectShape,
      style: {
        fill: api.visual('color'),
        stroke: '#1e3a8a',
        lineWidth: 1
      }
    };
  };

  const updateChart = () => {
    if (!chart) return;
    const calculatedHeight = Math.max(200, (slv.get_timelines().size * 50) + 100);

    const dom = chart.getDom();
    if (dom) {
      dom.style.height = `${calculatedHeight}px`;
    }

    chart.resize();
    chart.setOption(get_option(), true);
  };

  const solver_listener: solver.SolverListener = {
    initialized: () => { updateChart(); },
    new_flaw: (_flaw: solver.Flaw) => { },
    flaw_status_update: (_flaw: solver.Flaw) => { },
    flaw_cost_update: (_flaw: solver.Flaw | null) => { },
    current_flaw: (_flaw: solver.Flaw) => { },
    new_resolver: (_resolver: solver.Resolver) => { },
    resolver_status_update: (_resolver: solver.Resolver) => { },
    current_resolver: (_resolver: solver.Resolver | null) => { },
    new_causal_link: (_flaw: solver.Flaw, _resolver: solver.Resolver) => { },
    timelines_update: (_timelines: Map<string, solver.Timeline>) => { updateChart(); }
  };

  let resize_handler: () => void;

  return h('div#timelines-wrapper.flex-grow-1', {
    style: {
      height: '100%',
      overflowY: 'auto',
      minHeight: '0'
    }
  }, [
    h('div', {
      hook: {
        insert: (vnode) => {
          chart = echarts.init(vnode.elm as HTMLDivElement);

          updateChart();

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
    })
  ]);
}