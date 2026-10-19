import { h, VNode } from "snabbdom";
import { solver } from "../solver";
import * as echarts from 'echarts/core';
import { CustomChart } from "echarts/charts";
import { CanvasRenderer } from 'echarts/renderers';
import { GridComponent, TooltipComponent, DataZoomComponent, TitleComponent } from 'echarts/components';

echarts.use([CustomChart, CanvasRenderer, GridComponent, TooltipComponent, DataZoomComponent, TitleComponent]);

const esc = echarts.format.encodeHTML;

type IntervalRef =
  | { type: 'StateVariable'; objId: string; timeline: solver.StateVariableTimeline; interval: solver.StateVariableInterval }
  | { type: 'ReusableResource'; objId: string; timeline: solver.ReusableResourceTimeline; interval: solver.ReusableResourceInterval }
  | { type: 'ConsumableResource'; objId: string; timeline: solver.ConsumableResourceTimeline; interval: solver.ConsumableResourceInterval };

type IntervalDatum = {
  value: [number, number, number]; // [yIndex, start, end]
  itemStyle: { color: string; borderWidth: number; borderColor: string };
};

export function timelines(slv: solver.Solver): VNode {
  let chart: echarts.ECharts | undefined;

  let refs: IntervalRef[] = [];

  const atom_label = (id: string): string => {
    const atm = slv.get_atom(id);
    return atm ? atom(atm) : id;
  };

  const format_tooltip = (params: any): string => {
    const ref = refs[params.dataIndex];
    if (!ref) return '';

    const start = solver.num(ref.interval.start);
    const end = solver.num(ref.interval.end);
    const head = `<strong>${esc(ref.objId)}</strong> &middot; `;
    const common = `Start: ${start}<br/>End: ${end}<br/>Duration: ${end - start}`;

    switch (ref.type) {
      case 'StateVariable': {
        const n = ref.interval.atoms.length;
        const title = n === 0 ? 'Idle' : n === 1 ? 'Atom' : `Conflict (${n} atoms)`;
        const atoms = ref.interval.atoms.map(id => `&nbsp;&nbsp;${esc(atom_label(id))}`).join('<br/>');
        return `${head}${title}<br/>${common}${atoms ? `<br/>Atoms:<br/>${atoms}` : ''}`;
      }
      case 'ReusableResource': {
        const amount = solver.num(ref.interval.amount);
        const capacity = solver.num(ref.timeline.capacity);
        const usage = capacity > 0 ? ` (${((amount / capacity) * 100).toFixed(1)}%)` : '';
        const overload = amount > capacity ? '<br/><strong style="color:#ef4444">Over capacity</strong>' : '';
        return `${head}Reusable resource<br/>${common}<br/>Amount: ${amount} / ${capacity}${usage}${overload}`;
      }
      case 'ConsumableResource': {
        const from = solver.num(ref.interval.initial_amount);
        const to = solver.num(ref.interval.final_amount);
        const capacity = solver.num(ref.timeline.capacity);
        const delta = to - from;
        const violated = Math.min(from, to) < 0 || Math.max(from, to) > capacity;
        const warn = violated ? '<br/><strong style="color:#ef4444">Out of bounds</strong>' : '';
        return `${head}Consumable resource<br/>${common}<br/>Amount: ${from} &rarr; ${to} (${delta >= 0 ? '+' : ''}${delta})<br/>Capacity: ${capacity}${warn}`;
      }
    }
  };

  const get_option = (): echarts.EChartsCoreOption => {
    const categories: string[] = [];
    const data: IntervalDatum[] = [];
    const new_refs: IntervalRef[] = [];

    const add = (ref: IntervalRef, yIndex: number, color: string, borderColor: string) => {
      new_refs.push(ref);
      data.push({
        value: [yIndex, solver.num(ref.interval.start), solver.num(ref.interval.end)],
        itemStyle: { color, borderWidth: 1, borderColor }
      });
    };

    let yIndex = 0;
    for (const [id, timeline] of slv.get_timelines()) {
      const objId = `${id}`;
      categories.push(objId);

      switch (timeline.type) {
        case 'StateVariable':
          for (const interval of timeline.intervals) {
            const n = interval.atoms.length;
            add({ type: 'StateVariable', objId, timeline, interval }, yIndex,
              n == 0 ? '#9ca3af' : n == 1 ? '#3b82f6' : '#ef4444', '#1e3a8a');
          }
          break;
        case 'ReusableResource': {
          const capacity = solver.num(timeline.capacity);
          for (const interval of timeline.intervals) {
            add({ type: 'ReusableResource', objId, timeline, interval }, yIndex,
              solver.num(interval.amount) > capacity ? '#ef4444' : '#10b981', '#047857');
          }
          break;
        }
        case 'ConsumableResource': {
          const capacity = solver.num(timeline.capacity);
          for (const interval of timeline.intervals) {
            const from = solver.num(interval.initial_amount);
            const to = solver.num(interval.final_amount);
            const violated = Math.min(from, to) < 0 || Math.max(from, to) > capacity;
            add({ type: 'ConsumableResource', objId, timeline, interval }, yIndex,
              violated ? '#ef4444' : '#f59e0b', '#b45309');
          }
          break;
        }
      }

      yIndex++;
    }

    refs = new_refs;

    return {
      tooltip: { formatter: format_tooltip },
      dataZoom: [
        { type: 'slider', filterMode: 'weakFilter', showDataShadow: false, bottom: 20 },
        { type: 'inside', filterMode: 'weakFilter' }
      ],
      grid: { top: 30, right: 30, bottom: 70, left: 100 },
      xAxis: { type: 'value', scale: true },
      yAxis: { type: 'category', data: categories },
      series: [
        {
          type: 'custom',
          renderItem: renderGanttItem,
          encode: { x: [1, 2], y: 0 },
          data
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
      style: api.style()
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
    new_flaw: (_flaw: solver.Flaw) => { },
    flaw_status_update: (_flaw: solver.Flaw) => { },
    flaw_cost_update: (_flaw: solver.Flaw | null) => { },
    current_flaw: (_flaw: solver.Flaw) => { },
    new_resolver: (_resolver: solver.Resolver) => { },
    resolver_status_update: (_resolver: solver.Resolver) => { },
    current_resolver: (_resolver: solver.Resolver | null) => { },
    new_causal_link: (_flaw: solver.Flaw, _resolver: solver.Resolver) => { },
    to_solve_flaw: (_flaw: solver.Flaw) => { updateChart(); },
    solved_flaw: (_flaw: solver.Flaw) => { updateChart(); },
    state_update: () => { updateChart(); }
  };

  let resize_handler: () => void;

  return h('div#timelines-wrapper.flex-grow-1', {
    style: {
      height: '100%',
      width: '100%',
      overflowY: 'auto',
      minHeight: '0'
    }
  }, [
    h('div', {
      style: {
        width: '100%',
        height: '200px'
      },
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

function atom(atm: Readonly<solver.Atom>): string {
  return atm.get_predicate() + '(' + Object.entries(atm.get_env()).filter(([k, _v]) => k !== 'tau').map(([k, v]) => `${k}: ${solver.value_to_string(v)}`).join(', ') + ')';
}
