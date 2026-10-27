import { h, VNode } from "snabbdom";
import { solver } from "../solver";
import * as echarts from 'echarts/core';
import { CustomChart, LineChart } from "echarts/charts";
import { CanvasRenderer } from 'echarts/renderers';
import { GridComponent, TooltipComponent, DataZoomComponent, TitleComponent, MarkLineComponent } from 'echarts/components';

echarts.use([CustomChart, LineChart, CanvasRenderer, GridComponent, TooltipComponent, DataZoomComponent, TitleComponent, MarkLineComponent]);

const esc = echarts.format.encodeHTML;

const num = (r: solver.InfRational): number => r.num / r.den;

const LEFT = 60, RIGHT = 30, TOP = 10, BOTTOM = 70, HEADER = 20, GAP = 16;
const BODY: Record<solver.Timeline['type'], number> = {
  StateVariable: 50,
  ReusableResource: 110,
  ConsumableResource: 110
};

type IntervalRef =
  | { type: 'StateVariable'; objId: string; timeline: solver.StateVariableTimeline; interval: solver.StateVariableInterval }
  | { type: 'ReusableResource'; objId: string; timeline: solver.ReusableResourceTimeline; interval: solver.ReusableResourceInterval }
  | { type: 'ConsumableResource'; objId: string; timeline: solver.ConsumableResourceTimeline; interval: solver.ConsumableResourceInterval };

type IntervalDatum = {
  value: [number, number, number];
  itemStyle?: { color: string; borderWidth: number; borderColor: string };
};

type Span = { start: solver.InfRational; end: solver.InfRational };
const span = (i: Span): [number, number, number] => [0, num(i.start), num(i.end)];

function line_points<T extends Span>(intervals: T[], from: (i: T) => number, to: (i: T) => number): Array<[number, number | null]> {
  const pts: Array<[number, number | null]> = [];
  let prev_end: number | undefined;
  for (const i of intervals) {
    const s = num(i.start), e = num(i.end);
    if (prev_end !== undefined && s > prev_end) pts.push([prev_end, null]);
    pts.push([s, from(i)], [e, to(i)]);
    prev_end = e;
  }
  return pts;
}

const interval_rect = (params: any, api: any, full: boolean) => {
  const cs = params.coordSys;
  const s = api.coord([api.value(1), api.value(0)]);
  const e = api.coord([api.value(2), api.value(0)]);
  const height = full ? cs.height : api.size([0, 1])[1] * 0.6;
  return echarts.graphic.clipRectByRect({
    x: s[0],
    y: full ? cs.y : s[1] - height / 2,
    width: Math.max(e[0] - s[0], 2),
    height
  }, { x: cs.x, y: cs.y, width: cs.width, height: cs.height });
};

const render_bar = (params: any, api: any) => {
  const shape = interval_rect(params, api, false);
  return shape && { type: 'rect', transition: ['shape'], shape, style: api.style() };
};

const render_hit = (params: any, api: any) => {
  const shape = interval_rect(params, api, true);
  return shape && {
    type: 'rect',
    shape,
    style: { fill: 'rgba(0,0,0,0)' },
    emphasis: { style: { fill: 'rgba(100,116,139,0.18)' } }
  };
};

export function timelines(slv: solver.Solver): VNode {
  let chart: echarts.ECharts | undefined;
  let refs: (IntervalRef[] | undefined)[] = [];

  const atom_label = (id: string): string => {
    const atm = slv.get_atom(id);
    return atm ? atom(slv, atm) : id;
  };

  const format_tooltip = (params: any): string => {
    const ref = refs[params.seriesIndex]?.[params.dataIndex];
    if (!ref) return '';

    const start = num(ref.interval.start);
    const end = num(ref.interval.end);
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
        const amount = num(ref.interval.amount);
        const capacity = num(ref.timeline.capacity);
        const usage = capacity > 0 ? ` (${((amount / capacity) * 100).toFixed(1)}%)` : '';
        const overload = amount > capacity ? '<br/><strong style="color:#ef4444">Over capacity</strong>' : '';
        return `${head}Reusable resource<br/>${common}<br/>Amount: ${amount} / ${capacity}${usage}${overload}`;
      }
      case 'ConsumableResource': {
        const from = num(ref.interval.initial_amount);
        const to = num(ref.interval.final_amount);
        const capacity = num(ref.timeline.capacity);
        const delta = to - from;
        const violated = Math.min(from, to) < 0 || Math.max(from, to) > capacity;
        const warn = violated ? '<br/><strong style="color:#ef4444">Out of bounds</strong>' : '';
        return `${head}Consumable resource<br/>${common}<br/>Amount: ${from} &rarr; ${to} (${delta >= 0 ? '+' : ''}${delta})<br/>Capacity: ${capacity}${warn}`;
      }
    }
  };

  const build = (): { option: echarts.EChartsCoreOption; height: number } => {
    const timelines = slv.get_timelines();
    const count = timelines.size;
    if (count === 0) return { option: {}, height: 200 };

    let x_min = Infinity, x_max = -Infinity;
    for (const [, tl] of timelines) {
      for (const i of tl.intervals) {
        for (const v of [num(i.start), num(i.end)]) {
          if (Number.isFinite(v)) { x_min = Math.min(x_min, v); x_max = Math.max(x_max, v); }
        }
      }
    }
    if (!(x_min < x_max)) { x_min = 0; x_max = Math.max(1, x_min); }

    const titles: any[] = [];
    const grids: any[] = [];
    const x_axes: any[] = [];
    const y_axes: any[] = [];
    const series: any[] = [];
    const new_refs: (IntervalRef[] | undefined)[] = [];

    const add_series = (s: any, list?: IntervalRef[]) => {
      if (list) new_refs[series.length] = list;
      series.push(s);
    };

    const layer = (gi: number, renderItem: any, data: IntervalDatum[]) => ({
      type: 'custom', xAxisIndex: gi, yAxisIndex: gi, renderItem, encode: { x: [1, 2], y: 0 }, data
    });

    const value_axis = (gi: number, capacity: number) => ({
      type: 'value', gridIndex: gi, splitNumber: 2, axisLabel: { fontSize: 10 },
      min: (v: { min: number }) => Math.min(0, v.min),
      max: (v: { max: number }) => Math.max(capacity, v.max)
    });

    const line_series = (gi: number, points: Array<[number, number | null]>, capacity: number, color: string) => ({
      type: 'line', xAxisIndex: gi, yAxisIndex: gi,
      silent: true, showSymbol: false,
      lineStyle: { width: 2, color }, itemStyle: { color }, areaStyle: { color, opacity: 0.15 },
      data: points,
      markLine: {
        silent: true, symbol: 'none',
        lineStyle: { color: '#ef4444', type: 'dashed', width: 1 },
        label: { formatter: `capacity ${capacity}`, position: 'insideEndTop', fontSize: 10 },
        data: [{ yAxis: capacity }]
      }
    });

    let top = TOP;
    let gi = 0;
    for (const [id, timeline] of timelines) {
      const objId = `${id}`;
      const body = BODY[timeline.type];

      titles.push({ text: objId, left: LEFT, top, textStyle: { fontSize: 12, fontWeight: 'bold' } });
      top += HEADER;
      grids.push({ left: LEFT, right: RIGHT, top, height: body });
      top += body + GAP;

      x_axes.push({
        type: 'value', gridIndex: gi, min: x_min, max: x_max,
        axisLabel: { show: gi === count - 1 },
        splitLine: { show: true, lineStyle: { opacity: 0.25 } }
      });

      switch (timeline.type) {
        case 'StateVariable': {
          y_axes.push({ type: 'category', gridIndex: gi, data: [objId], show: false });
          const list: IntervalRef[] = [];
          const data: IntervalDatum[] = [];
          for (const interval of timeline.intervals) {
            const n = interval.atoms.length;
            list.push({ type: 'StateVariable', objId, timeline, interval });
            data.push({
              value: span(interval),
              itemStyle: {
                color: n == 0 ? '#9ca3af' : n == 1 ? '#3b82f6' : '#ef4444',
                borderWidth: 1,
                borderColor: '#1e3a8a'
              }
            });
          }
          add_series(layer(gi, render_bar, data), list);
          break;
        }
        case 'ReusableResource': {
          const capacity = num(timeline.capacity);
          y_axes.push(value_axis(gi, capacity));
          add_series(line_series(gi, line_points(timeline.intervals, i => num(i.amount), i => num(i.amount)), capacity, '#10b981'));
          const list: IntervalRef[] = [];
          const data: IntervalDatum[] = [];
          for (const interval of timeline.intervals) {
            list.push({ type: 'ReusableResource', objId, timeline, interval });
            data.push({ value: span(interval) });
          }
          add_series(layer(gi, render_hit, data), list);
          break;
        }
        case 'ConsumableResource': {
          const capacity = num(timeline.capacity);
          y_axes.push(value_axis(gi, capacity));
          add_series(line_series(gi, line_points(timeline.intervals, i => num(i.initial_amount), i => num(i.final_amount)), capacity, '#f59e0b'));
          const list: IntervalRef[] = [];
          const data: IntervalDatum[] = [];
          for (const interval of timeline.intervals) {
            list.push({ type: 'ConsumableResource', objId, timeline, interval });
            data.push({ value: span(interval) });
          }
          add_series(layer(gi, render_hit, data), list);
          break;
        }
      }

      gi++;
    }

    refs = new_refs;

    const all_x = x_axes.map((_, i) => i);
    return {
      height: Math.max(200, top + BOTTOM),
      option: {
        tooltip: { trigger: 'item', formatter: format_tooltip },
        title: titles,
        grid: grids,
        xAxis: x_axes,
        yAxis: y_axes,
        dataZoom: [
          { type: 'slider', xAxisIndex: all_x, filterMode: 'none', showDataShadow: false, bottom: 20 },
          { type: 'inside', xAxisIndex: all_x, filterMode: 'none' }
        ],
        series
      }
    };
  };

  const updateChart = () => {
    if (!chart) return;
    const { option, height } = build();

    const dom = chart.getDom();
    if (dom) {
      dom.style.height = `${height}px`;
    }

    chart.resize();
    chart.setOption(option, true);
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

function atom(slv: solver.Solver, atm: Readonly<solver.Atom>): string {
  return atm.get_predicate() + '(' + Object.entries(atm.get_env()).filter(([k, _v]) => k !== 'tau').map(([k, v]) => `${k}: ${solver.value_to_string(slv, v)}`).join(', ') + ')';
}