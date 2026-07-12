import React, { useState, useMemo, useRef, useEffect } from "react";

/* ================================================================
   SUB-BEAM 2D — 연속보·부분골조 해석 (직접강성법)
   절점당 2자유도(v, θ), 지점 v=0 구속, 기둥은 원단고정 회전스프링(4EI/H)
   검증: 단순보 wL²/8 · 2경간 −wL²/8 · 삼각형 wL²/(9√3) · 캔틸레버 −wl²/2
         고정단 −wL²/12 · 처짐 5wL⁴/384EI 등 이론해 32항목 일치 확인
   ================================================================ */

/* ---------------- solver ---------------- */

function solveLinear(A, b) {
  const n = b.length;
  const M = A.map((row, i) => [...row, b[i]]);
  for (let c = 0; c < n; c++) {
    let p = c;
    for (let r = c + 1; r < n; r++) if (Math.abs(M[r][c]) > Math.abs(M[p][c])) p = r;
    [M[c], M[p]] = [M[p], M[c]];
    const pv = M[c][c];
    if (Math.abs(pv) < 1e-14) throw new Error("특이행렬 — 입력값을 확인하세요");
    for (let r = 0; r < n; r++) {
      if (r === c) continue;
      const f = M[r][c] / pv;
      for (let k = c; k <= n; k++) M[r][k] -= f * M[c][k];
    }
  }
  return M.map((row, i) => row[n] / M[i][i]);
}

function beamK(EI, L) {
  const L2 = L * L, L3 = L2 * L;
  return [
    [12 * EI / L3, 6 * EI / L2, -12 * EI / L3, 6 * EI / L2],
    [6 * EI / L2, 4 * EI / L, -6 * EI / L2, 2 * EI / L],
    [-12 * EI / L3, -6 * EI / L2, 12 * EI / L3, -6 * EI / L2],
    [6 * EI / L2, 2 * EI / L, -6 * EI / L2, 4 * EI / L],
  ];
}

/* 모든 분포하중을 선형 piece {w1, w2, a, b} 목록으로 정규화
   — udl·삼각형·부분 등분포·사다리꼴을 하나의 수식 체계로 처리 */
const clampv = (v, lo, hi) => Math.min(hi, Math.max(lo, v));
function piecesOf(load, L) {
  const t = load.type, w = load.w;
  if (t === "udl") return [{ w1: w, w2: w, a: 0, b: L }];
  if (t === "triAsc") return [{ w1: 0, w2: w, a: 0, b: L }];
  if (t === "triDesc") return [{ w1: w, w2: 0, a: 0, b: L }];
  if (t === "triSym") return [{ w1: 0, w2: w, a: 0, b: L / 2 }, { w1: w, w2: 0, a: L / 2, b: L }];
  if (t === "partUdl" || t === "trap") {
    let a = clampv(load.a ?? 0, 0, L), b = clampv(load.b ?? L, 0, L);
    if (b < a) [a, b] = [b, a];
    if (b - a < 1e-9) return [];
    if (t === "partUdl") return [{ w1: w, w2: w, a, b }];
    return [{ w1: load.w1 ?? w, w2: load.w2 ?? w, a, b }];
  }
  if (t === "trapSym") { // 2방향 슬래브형: 0→w 램프 s, 중앙 일정, w→0 램프 s
    const s = clampv(load.s ?? L / 4, 0.001, L / 2);
    const ps = [{ w1: 0, w2: w, a: 0, b: s }];
    if (L - 2 * s > 1e-9) ps.push({ w1: w, w2: w, a: s, b: L - s });
    ps.push({ w1: w, w2: 0, a: L - s, b: L });
    return ps;
  }
  if (t === "triN") { // 등간격 연속 삼각형 n개 (n=2: 중앙 기준 양쪽 2개)
    const n = Math.max(1, Math.min(12, Math.round(load.n ?? 2)));
    const seg = L / n, ps = [];
    for (let i = 0; i < n; i++) {
      const a = i * seg, m = a + seg / 2, b = a + seg;
      ps.push({ w1: 0, w2: w, a, b: m });
      ps.push({ w1: w, w2: 0, a: m, b });
    }
    return ps;
  }
  if (t === "triValley") return [{ w1: w, w2: 0, a: 0, b: L / 2 }, { w1: 0, w2: w, a: L / 2, b: L }];
  return [];
}

/* piece 고정단력 — 3점 가우스 적분 (피적분식이 4차 다항식이므로 엄밀해) */
const GP = [-Math.sqrt(3 / 5), 0, Math.sqrt(3 / 5)];
const GW = [5 / 9, 8 / 9, 5 / 9];
function fefPiece(p, L) {
  const { w1, w2, a, b } = p;
  const half = (b - a) / 2, mid = (a + b) / 2;
  const f = [0, 0, 0, 0];
  for (let i = 0; i < 3; i++) {
    const xi = mid + half * GP[i];
    const wv = w1 + (w2 - w1) * (xi - a) / (b - a);
    const eta = L - xi;
    const phi = [
      eta * eta * (3 * xi + eta) / (L ** 3),
      xi * eta * eta / (L * L),
      xi * xi * (xi + 3 * eta) / (L ** 3),
      -xi * xi * eta / (L * L),
    ];
    for (let k = 0; k < 4; k++) f[k] += GW[i] * half * wv * phi[k];
  }
  return f;
}

/* 고정단력 f0 = 절점이 요소에 가하는 힘 (상향+, 반시계+) / 하중은 하향+ */
function fixedEndForces(load, L) {
  const t = load.type;
  if (t === "point" || t === "pointCenter") {
    const P = load.P;
    const a = t === "pointCenter" ? L / 2 : clampv(load.a, 0, L);
    const b = L - a;
    return [
      P * b * b * (3 * a + b) / (L ** 3),
      P * a * b * b / (L * L),
      P * a * a * (a + 3 * b) / (L ** 3),
      -P * a * a * b / (L * L),
    ];
  }
  const f = [0, 0, 0, 0];
  piecesOf(load, L).forEach(p => {
    const g = fefPiece(p, L);
    for (let k = 0; k < 4; k++) f[k] += g[k];
  });
  return f;
}

/* piece 누적하중 W(x)와 절단면 기준 1차모멘트 Mw(x) */
function pieceIntegrals(p, x) {
  const { w1, w2, a, b } = p;
  if (x <= a) return [0, 0];
  const c = b - a, m = (w2 - w1) / c;
  if (x <= b) {
    const t = x - a;
    return [w1 * t + m * t * t / 2, w1 * t * t / 2 + m * t ** 3 / 6];
  }
  const Q = (w1 + w2) / 2 * c;
  const Mwb = w1 * c * c / 2 + m * c ** 3 / 6;
  return [Q, Mwb + Q * (x - b)];
}

function distLoadIntegrals(load, L, x) {
  let W = 0, Mw = 0;
  piecesOf(load, L).forEach(p => {
    const [w_, mw_] = pieceIntegrals(p, x);
    W += w_; Mw += mw_;
  });
  return [W, Mw];
}

function pointLoadsOf(load, L) {
  if (load.type === "point") return [{ P: load.P, a: Math.min(Math.max(load.a, 0), L) }];
  if (load.type === "pointCenter") return [{ P: load.P, a: L / 2 }];
  return [];
}

function totalOf(load, L) {
  if (load.type === "point" || load.type === "pointCenter") return load.P;
  return piecesOf(load, L).reduce((s, p) => s + (p.w1 + p.w2) / 2 * (p.b - p.a), 0);
}

function analyze(model) {
  const Ek = model.E * 1000; // MPa → kN/m²
  const EIof = (b, h) => Ek * ((b * Math.pow(h, 3)) / 12) * 1e-12; // kN·m²

  const segs = [];
  if (model.cantL && model.cantL.on) segs.push({ kind: "cantL", ...JSON.parse(JSON.stringify(model.cantL)) });
  model.spans.forEach((s, i) => segs.push({ kind: "span", idx: i, ...JSON.parse(JSON.stringify(s)) }));
  if (model.cantR && model.cantR.on) segs.push({ kind: "cantR", ...JSON.parse(JSON.stringify(model.cantR)) });

  segs.forEach(s => {
    if (!(s.L > 0)) throw new Error("부재 길이는 0보다 커야 합니다");
    s.EI = EIof(s.b, s.h);
    s.loads = (s.loads || []).map(ld => ({ ...ld }));
    if (model.selfWeight) {
      s.loads.push({ type: "udl", w: model.gamma * (s.b / 1000) * (s.h / 1000), self: true });
    }
  });

  const nNodes = segs.length + 1;
  const firstJ = model.cantL && model.cantL.on ? 1 : 0;
  const nSup = model.spans.length + 1;
  const junctionNodes = [];
  for (let i = 0; i < nSup; i++) junctionNodes.push(firstJ + i);

  const ndof = 2 * nNodes;
  const K = Array.from({ length: ndof }, () => new Array(ndof).fill(0));
  const F = new Array(ndof).fill(0);

  segs.forEach((s, e) => {
    const k = beamK(s.EI, s.L);
    const f0 = [0, 0, 0, 0];
    s.loads.forEach(ld => {
      const f = fixedEndForces(ld, s.L);
      for (let i = 0; i < 4; i++) f0[i] += f[i];
    });
    s.f0 = f0;
    const dofs = [2 * e, 2 * e + 1, 2 * (e + 1), 2 * (e + 1) + 1];
    for (let i = 0; i < 4; i++) {
      F[dofs[i]] -= f0[i];
      for (let j = 0; j < 4; j++) K[dofs[i]][dofs[j]] += k[i][j];
    }
    s.dofs = dofs;
  });

  /* 기둥 회전스프링 (원단 고정: k=4EI/H, 이월 2EI/H) */
  const colInfo = [];
  junctionNodes.forEach((nd, i) => {
    const sup = model.supports[i];
    let kth = 0;
    const info = { support: i, node: nd, low: null, up: null };
    ["low", "up"].forEach(key => {
      const c = sup && sup[key];
      if (c && c.on && c.H > 0) {
        const EIc = EIof(c.b, c.h);
        info[key] = { H: c.H, b: c.b, h: c.h, kNear: 4 * EIc / c.H, kFar: 2 * EIc / c.H };
        kth += info[key].kNear;
      }
    });
    K[2 * nd + 1][2 * nd + 1] += kth;
    info.kth = kth;
    colInfo.push(info);
  });

  /* 경계조건: 지점 v = 0 */
  const fixed = new Set(junctionNodes.map(nd => 2 * nd));
  const free = [];
  for (let dd = 0; dd < ndof; dd++) if (!fixed.has(dd)) free.push(dd);
  const Kff = free.map(r => free.map(c => K[r][c]));
  const Ff = free.map(r => F[r]);
  const df = solveLinear(Kff, Ff);
  const d = new Array(ndof).fill(0);
  free.forEach((dof, i) => { d[dof] = df[i]; });

  /* 요소 단부력 S = k·d + f0 */
  segs.forEach(s => {
    const k = beamK(s.EI, s.L);
    const de = s.dofs.map(i => d[i]);
    s.S = [0, 1, 2, 3].map(i => k[i].reduce((acc, kij, j) => acc + kij * de[j], 0) + s.f0[i]);
  });

  /* 반력 */
  const reactions = junctionNodes.map(nd => {
    let R = 0;
    segs.forEach((s, e) => {
      if (e === nd) R += s.S[0];
      if (e + 1 === nd) R += s.S[2];
    });
    return R;
  });

  /* 기둥 단부모멘트 */
  colInfo.forEach(ci => {
    const th = d[2 * ci.node + 1];
    ci.theta = th;
    ["low", "up"].forEach(key => {
      if (ci[key]) {
        ci[key].Mnear = ci[key].kNear * th;
        ci[key].Mfar = ci[key].kFar * th;
        ci[key].V = (ci[key].Mnear + ci[key].Mfar) / ci[key].H;
      }
    });
  });

  /* 내력도 샘플링 + 처짐(곡률 이중적분, 선형 폐합보정) */
  const NS = 240;
  let x0 = 0;
  const nodeX = [0];
  segs.forEach(s => {
    const pls = [];
    s.loads.forEach(ld => pointLoadsOf(ld, s.L).forEach(p => pls.push(p)));
    const xs = [];
    for (let i = 0; i <= NS; i++) xs.push(s.L * i / NS);
    pls.forEach(p => { xs.push(Math.max(p.a - 1e-9, 0)); xs.push(Math.min(p.a + 1e-9, s.L)); });
    s.loads.forEach(ld => piecesOf(ld, s.L).forEach(pc => { xs.push(pc.a); xs.push(pc.b); }));
    xs.sort((a, b) => a - b);
    const V1 = s.S[0], M1 = -s.S[1];
    const pts = xs.map(x => {
      let W = 0, Mw = 0;
      s.loads.forEach(ld => {
        const [w_, mw_] = distLoadIntegrals(ld, s.L, x);
        W += w_; Mw += mw_;
      });
      let V = V1 - W, M = M1 + V1 * x - Mw;
      pls.forEach(p => {
        if (x > p.a + 1e-12 || Math.abs(x - (p.a + 1e-9)) < 1e-12) {
          V -= p.P; M -= p.P * (x - p.a);
        }
      });
      return { x, xg: x0 + x, V, M };
    });
    /* 처짐 */
    const dv1 = d[s.dofs[0]], dth1 = d[s.dofs[1]], dv2 = d[s.dofs[2]];
    const th = [dth1], vv = [dv1];
    for (let i = 1; i < pts.length; i++) {
      const dx = pts[i].x - pts[i - 1].x;
      th.push(th[i - 1] + 0.5 * (pts[i].M + pts[i - 1].M) / s.EI * dx);
      vv.push(vv[i - 1] + 0.5 * (th[i] + th[i - 1]) * dx);
    }
    const err = vv[vv.length - 1] - dv2;
    pts.forEach((p, i) => { p.defl = vv[i] - err * p.x / s.L; });
    s.diagram = pts;
    s.x0 = x0;
    x0 += s.L;
    nodeX.push(x0);
  });
  const totalL = x0;
  const junctionXg = junctionNodes.map(nd => nodeX[nd]);

  /* 평형 검토 */
  let totalLoad = 0;
  segs.forEach(s => s.loads.forEach(ld => { totalLoad += totalOf(ld, s.L); }));
  const sumR = reactions.reduce((a, b) => a + b, 0);

  /* 자유도 라벨 */
  const nodeNames = [];
  for (let k2 = 0; k2 < nNodes; k2++) {
    if (model.cantL && model.cantL.on && k2 === 0) nodeNames.push("좌측 자유단");
    else if (model.cantR && model.cantR.on && k2 === nNodes - 1) nodeNames.push("우측 자유단");
    else nodeNames.push(`지점${k2 - firstJ + 1}`);
  }
  const dofLabels = free.map(dof => `${dof % 2 ? "θ" : "v"} · ${nodeNames[dof >> 1]}`);

  return { segs, reactions, colInfo, d, junctionNodes, nodeX, junctionXg, totalL, Kff, Ff, df, dofLabels, totalLoad, sumR };
}

/* ---------------- utils ---------------- */

const uid = () => Math.random().toString(36).slice(2, 9);
const fmt = (v, dec = 1) => {
  if (!Number.isFinite(v)) return "–";
  const s = Math.abs(v) < 0.5 * Math.pow(10, -dec) ? 0 : v;
  return s.toLocaleString("en-US", { minimumFractionDigits: dec, maximumFractionDigits: dec });
};
const CIRC = ["①", "②", "③", "④", "⑤", "⑥", "⑦", "⑧", "⑨", "⑩"];

const C = {
  ink: "#1C2B33", sub: "#5C6B66", line: "#DADFD8", grid: "#C7CEC5",
  paper: "#F1F3EF", panel: "#FFFFFF",
  shear: "#0F7B8A", moment: "#B0413E", defl: "#6E62A8",
  load: "#C87A14", col: "#5B6670",
};

const LOAD_TYPES = [
  { v: "udl", label: "등분포 w" },
  { v: "point", label: "집중하중 P (위치 a)" },
  { v: "pointCenter", label: "중앙 집중하중 P" },
  { v: "triAsc", label: "삼각형 (좌 0 → 우 최대)" },
  { v: "triDesc", label: "삼각형 (좌 최대 → 우 0)" },
  { v: "triSym", label: "삼각형 (중앙 최대)" },
  { v: "triN", label: "삼각형 n개 (등간격 연속)" },
  { v: "triValley", label: "삼각형 (양단 최대 → 중앙 0)" },
  { v: "partUdl", label: "부분 등분포 w (a~b)" },
  { v: "trap", label: "사다리꼴 w₁→w₂ (a~b)" },
  { v: "trapSym", label: "사다리꼴 (2방향 슬래브형)" },
];

const newLoad = (type = "udl", segL = 6) => ({ id: uid(), type, w: 30, P: 50, a: 1, b: segL, w1: 20, w2: 40, s: segL / 4, n: 2 });
const newSupport = () => ({
  low: { on: true, H: 4.0, b: 500, h: 500 },
  up: { on: true, H: 3.5, b: 500, h: 500 },
});
const makeDefaultModel = () => ({
  E: 25000, selfWeight: false, gamma: 24,
  spans: [
    { L: 7, b: 400, h: 700, loads: [{ id: uid(), type: "triN", w: 45, P: 50, a: 1, n: 2 }] },
    { L: 9, b: 400, h: 700, loads: [
      { id: uid(), type: "trapSym", w: 55, P: 50, a: 1, s: 2.25 },
      { id: uid(), type: "pointCenter", w: 30, P: 80, a: 1 },
    ] },
  ],
  supports: [newSupport(), newSupport(), newSupport()],
  cantL: { on: false, L: 1.5, b: 400, h: 700, loads: [newLoad()] },
  cantR: { on: true, L: 2.0, b: 400, h: 700, loads: [{ id: uid(), type: "udl", w: 40, P: 50, a: 1 }] },
});

/* ---------------- 소형 입력 컴포넌트 ---------------- */

function Num({ label, unit, value, onChange, step = 1, min, width = 74 }) {
  const [txt, setTxt] = useState(String(value));
  const editing = useRef(false);
  useEffect(() => { if (!editing.current) setTxt(String(value)); }, [value]);
  return (
    <label className="num">
      {label && <span className="nl">{label}</span>}
      <input
        type="number" value={txt} step={step} min={min} style={{ width }}
        onFocus={() => { editing.current = true; }}
        onBlur={() => { editing.current = false; setTxt(String(value)); }}
        onChange={e => {
          setTxt(e.target.value);
          const v = parseFloat(e.target.value);
          if (Number.isFinite(v)) onChange(min !== undefined ? Math.max(min, v) : v);
        }}
      />
      {unit && <span className="nu">{unit}</span>}
    </label>
  );
}

function Chk({ label, checked, onChange }) {
  return (
    <label className="chk">
      <input type="checkbox" checked={checked} onChange={e => onChange(e.target.checked)} />
      <span>{label}</span>
    </label>
  );
}

const W_TYPES = ["udl", "triAsc", "triDesc", "triSym", "triN", "triValley", "partUdl", "trapSym"];
function LoadsEditor({ loads, onChange, segL = 6 }) {
  const update = (i, patch) => onChange(loads.map((ld, j) => (j === i ? { ...ld, ...patch } : ld)));
  const remove = i => onChange(loads.filter((_, j) => j !== i));
  return (
    <div className="loads">
      {loads.map((ld, i) => (
        <div className="loadrow" key={ld.id}>
          <select value={ld.type} onChange={e => update(i, { type: e.target.value })}>
            {LOAD_TYPES.map(t => <option key={t.v} value={t.v}>{t.label}</option>)}
          </select>
          {W_TYPES.includes(ld.type) && (
            <Num value={ld.w} onChange={v => update(i, { w: v })} unit="kN/m" step={1} width={62} />
          )}
          {ld.type === "triN" && (
            <Num label="n" value={ld.n ?? 2} onChange={v => update(i, { n: v })} unit="개" step={1} min={1} width={46} />
          )}
          {ld.type === "trap" && (<>
            <Num label="w₁" value={ld.w1 ?? ld.w} onChange={v => update(i, { w1: v })} step={1} width={52} />
            <Num label="w₂" value={ld.w2 ?? ld.w} onChange={v => update(i, { w2: v })} unit="kN/m" step={1} width={52} />
          </>)}
          {(ld.type === "point" || ld.type === "pointCenter") && (
            <Num value={ld.P} onChange={v => update(i, { P: v })} unit="kN" step={1} width={62} />
          )}
          {(ld.type === "point" || ld.type === "partUdl" || ld.type === "trap") && (
            <Num label="a" value={ld.a} onChange={v => update(i, { a: v })} unit="m" step={0.1} min={0} width={54} />
          )}
          {(ld.type === "partUdl" || ld.type === "trap") && (
            <Num label="b" value={ld.b ?? segL} onChange={v => update(i, { b: v })} unit="m" step={0.1} min={0} width={54} />
          )}
          {ld.type === "trapSym" && (
            <Num label="램프 s" value={ld.s ?? segL / 4} onChange={v => update(i, { s: v })} unit="m" step={0.05} min={0.05} width={56} />
          )}
          <button className="xbtn" onClick={() => remove(i)} aria-label="하중 삭제">×</button>
        </div>
      ))}
      <button className="addbtn" onClick={() => onChange([...loads, newLoad("udl", segL)])}>＋ 하중 추가</button>
    </div>
  );
}

/* ---------------- 플롯 공통 ---------------- */

function useWidth(ref, fallback = 860) {
  const [w, setW] = useState(fallback);
  useEffect(() => {
    if (!ref.current || typeof ResizeObserver === "undefined") return;
    const ro = new ResizeObserver(es => { for (const e of es) setW(Math.max(320, e.contentRect.width)); });
    ro.observe(ref.current);
    return () => ro.disconnect();
  }, [ref]);
  return w;
}

const ML = 18, MR = 18;

function valueAt(pts, hx) {
  if (!pts.length) return null;
  if (hx <= pts[0].xg) return pts[0].val;
  for (let i = 0; i < pts.length - 1; i++) {
    if (hx >= pts[i].xg && hx <= pts[i + 1].xg) {
      const dx = pts[i + 1].xg - pts[i].xg;
      if (dx < 1e-9) return pts[i].val;
      return pts[i].val + (pts[i + 1].val - pts[i].val) * (hx - pts[i].xg) / dx;
    }
  }
  return pts[pts.length - 1].val;
}

function usePointer(totalL, w, setHoverX) {
  return {
    onPointerMove: e => {
      const r = e.currentTarget.getBoundingClientRect();
      const x = ((e.clientX - r.left) - ML) / (w - ML - MR) * totalL;
      setHoverX(Math.max(0, Math.min(totalL, x)));
    },
    onPointerLeave: () => setHoverX(null),
  };
}

function DiagramPlot({ title, unit, color, pts, labels, invert, height, w, totalL, junctionXg, hoverX, setHoverX, showXAxis, dec = 1, deflMode = false }) {
  const sx = x => ML + (x / totalL) * (w - ML - MR);
  const padT = 26, padB = showXAxis ? 24 : 12;
  const vmax = Math.max(1e-9, ...pts.map(p => Math.abs(p.val))) * 1.14;
  const zeroY = padT + (height - padT - padB) / 2;
  const scale = (height - padT - padB) / 2 / vmax;
  const yOf = v => (invert ? zeroY + v * scale : zeroY - v * scale);

  let dPath = "", fPath = "";
  pts.forEach((p, i) => {
    const cmd = `${i === 0 ? "M" : "L"}${sx(p.xg).toFixed(2)},${yOf(p.val).toFixed(2)}`;
    dPath += cmd;
  });
  if (pts.length) {
    fPath = `M${sx(pts[0].xg).toFixed(2)},${zeroY.toFixed(2)}` +
      pts.map(p => `L${sx(p.xg).toFixed(2)},${yOf(p.val).toFixed(2)}`).join("") +
      `L${sx(pts[pts.length - 1].xg).toFixed(2)},${zeroY.toFixed(2)}Z`;
  }

  const hv = hoverX != null ? valueAt(pts, hoverX) : null;
  const handlers = usePointer(totalL, w, setHoverX);

  const fmtVal = v => (deflMode ? `${fmt(Math.abs(v), dec)}${v < -1e-9 ? "↓" : v > 1e-9 ? "↑" : ""}` : fmt(v, dec));

  return (
    <svg className="plot" width={w} height={height} viewBox={`0 0 ${w} ${height}`} preserveAspectRatio="xMidYMid meet" {...handlers}>
      <text x={ML} y={15} className="ptitle" fill={color}>{title}</text>
      {hoverX != null && hv != null && (
        <text x={w - MR} y={15} textAnchor="end" className="preadout" fill={C.ink}>
          x = {fmt(hoverX, 2)} m &nbsp;·&nbsp; {fmtVal(hv)} {unit}
        </text>
      )}
      {junctionXg.map((xj, i) => (
        <line key={i} x1={sx(xj)} x2={sx(xj)} y1={padT - 4} y2={height - padB} stroke={C.grid} strokeDasharray="3 4" strokeWidth="1" />
      ))}
      <line x1={ML} x2={w - MR} y1={zeroY} y2={zeroY} stroke={C.ink} strokeWidth="1" />
      <text x={ML - 3} y={zeroY + 3} textAnchor="end" className="pzero" fill={C.sub}>0</text>
      <path d={fPath} fill={color} fillOpacity="0.13" />
      <path d={dPath} fill="none" stroke={color} strokeWidth="1.8" strokeLinejoin="round" />
      {labels.map((lb, i) => {
        const lx = Math.max(ML + 14, Math.min(w - MR - 14, sx(lb.xg)));
        const above = invert ? lb.val < 0 : lb.val > 0;
        let ly = yOf(lb.val) + (above ? -6 : 14);
        ly = Math.max(padT - 8, Math.min(height - 4, ly));
        return (
          <text key={i} x={lx} y={ly} textAnchor="middle" className="plabel" fill={color}
            stroke="#fff" strokeWidth="3" paintOrder="stroke">{fmtVal(lb.val)}</text>
        );
      })}
      {hoverX != null && (
        <g>
          <line x1={sx(hoverX)} x2={sx(hoverX)} y1={padT - 6} y2={height - padB} stroke={C.ink} strokeWidth="1" strokeDasharray="2 3" opacity="0.7" />
          {hv != null && <circle cx={sx(hoverX)} cy={yOf(hv)} r="3.4" fill="#fff" stroke={color} strokeWidth="2" />}
        </g>
      )}
      {showXAxis && (
        <g className="xaxis">
          {[0, ...junctionXg, totalL]
            .filter((v, i, arr) => arr.findIndex(u => Math.abs(u - v) < 1e-6) === i)
            .map((xv, i) => (
              <text key={i} x={sx(xv)} y={height - 8} textAnchor="middle" fill={C.sub}>{fmt(xv, 1)}</text>
            ))}
          <text x={w - MR} y={height - 8} textAnchor="end" fill={C.sub}>x (m)</text>
        </g>
      )}
    </svg>
  );
}

/* ---------------- 모델도 ---------------- */

function Arrow({ x, y1, y2, color = C.load, sw = 1.6 }) {
  return (
    <g>
      <line x1={x} x2={x} y1={y1} y2={y2 - 6} stroke={color} strokeWidth={sw} />
      <polygon points={`${x},${y2} ${x - 3.6},${y2 - 7} ${x + 3.6},${y2 - 7}`} fill={color} />
    </g>
  );
}

function ModelView({ res, model, w, hoverX, setHoverX }) {
  const H = 172;
  const { totalL, nodeX, junctionXg, reactions, junctionNodes, segs } = res;
  const sx = x => ML + (x / totalL) * (w - ML - MR);
  const yB = 62;             // 보 상단
  const beamH = 6;
  const dimY = 154;
  const handlers = usePointer(totalL, w, setHoverX);

  const drawLoad = (s, ld, li) => {
    const x0 = sx(s.x0), x1 = sx(s.x0 + s.L);
    const bandTop = yB - 40, bandBot = yB - 2;
    const key = `${s.x0}-${li}`;
    if (ld.self) return null;
    if (ld.type === "point" || ld.type === "pointCenter") {
      const a = ld.type === "pointCenter" ? s.L / 2 : Math.min(Math.max(ld.a, 0), s.L);
      const xp = sx(s.x0 + a);
      return (
        <g key={key}>
          <Arrow x={xp} y1={yB - 54} y2={yB - 1} sw={2.2} />
          <text x={xp} y={yB - 57} textAnchor="middle" className="loadlbl" fill={C.load}
            stroke="#fff" strokeWidth="3" paintOrder="stroke">{fmt(ld.P, 0)} kN</text>
        </g>
      );
    }
    /* 분포하중 형상 — 선형 piece 기반 (부분 구간·사다리꼴 포함) */
    const pieces = piecesOf(ld, s.L);
    if (!pieces.length) return null;
    const hMax = 34;
    const topAt = frac => bandBot - 2 - frac * hMax;
    const wmaxA = Math.max(1e-9, ...pieces.flatMap(p => [Math.abs(p.w1), Math.abs(p.w2)]));
    const wAt = xm => {
      for (const p of pieces) {
        if (xm >= p.a - 1e-9 && xm <= p.b + 1e-9) return p.w1 + (p.w2 - p.w1) * (xm - p.a) / (p.b - p.a);
      }
      return 0;
    };
    const polys = pieces.map((p, pi) => {
      const xa = sx(s.x0 + p.a), xb = sx(s.x0 + p.b);
      const f1 = Math.abs(p.w1) / wmaxA, f2 = Math.abs(p.w2) / wmaxA;
      return (
        <polygon key={pi} points={`${xa},${topAt(f1)} ${xb},${topAt(f2)} ${xb},${bandBot} ${xa},${bandBot}`}
          fill={C.load} fillOpacity="0.14" stroke={C.load} strokeWidth="1.1" />
      );
    });
    const aMin = Math.min(...pieces.map(p => p.a)), bMax = Math.max(...pieces.map(p => p.b));
    const xA = sx(s.x0 + aMin), xB = sx(s.x0 + bMax);
    const n = Math.max(3, Math.floor((xB - xA) / 30));
    const arrows = [];
    for (let i = 0; i <= n; i++) {
      const xm = aMin + (bMax - aMin) * (i / n);
      const f = Math.abs(wAt(xm)) / wmaxA;
      if (f < 0.06) continue;
      arrows.push(<Arrow key={i} x={sx(s.x0 + xm)} y1={topAt(f)} y2={bandBot} sw={1.3} />);
    }
    const lblTxt = ld.type === "trap"
      ? `w=${fmt(pieces[0].w1, 0)}→${fmt(pieces[0].w2, 0)} kN/m`
      : `w = ${fmt(ld.w, 0)} kN/m`;
    return (
      <g key={key} opacity="0.92">
        {polys}
        {arrows}
        <text x={(xA + xB) / 2} y={bandTop - 4 - li * 11} textAnchor="middle" className="loadlbl" fill={C.load}
          stroke="#fff" strokeWidth="3" paintOrder="stroke">{lblTxt}</text>
      </g>
    );
  };

  return (
    <svg className="plot" width={w} height={H} viewBox={`0 0 ${w} ${H}`} preserveAspectRatio="xMidYMid meet" {...handlers}>
      <text x={ML} y={15} className="ptitle" fill={C.ink}>구조 모델</text>
      {hoverX != null && (
        <text x={w - MR} y={15} textAnchor="end" className="preadout" fill={C.ink}>x = {fmt(hoverX, 2)} m</text>
      )}
      {model.selfWeight && (
        <text x={ML + 78} y={15} className="pzero" fill={C.sub}>자중 포함 (γ={model.gamma} kN/m³)</text>
      )}

      {/* 기둥 */}
      {res.colInfo.map((ci, i) => {
        const x = sx(junctionXg[i]);
        const parts = [];
        if (ci.up) {
          const yT = yB - 42;
          parts.push(<rect key="u" x={x - 5.5} y={yT} width={11} height={42} fill="#fff" stroke={C.col} strokeWidth="1.5" />);
          parts.push(<line key="uc" x1={x - 10} x2={x + 10} y1={yT} y2={yT} stroke={C.col} strokeWidth="1.8" />);
          for (let k = 0; k < 4; k++) parts.push(<line key={"uh" + k} x1={x - 9 + k * 6} x2={x - 4 + k * 6} y1={yT} y2={yT - 5} stroke={C.col} strokeWidth="1" />);
        }
        if (ci.low) {
          const yBt = yB + beamH, yBs = yBt + 42;
          parts.push(<rect key="l" x={x - 5.5} y={yBt} width={11} height={42} fill="#fff" stroke={C.col} strokeWidth="1.5" />);
          parts.push(<line key="lc" x1={x - 10} x2={x + 10} y1={yBs} y2={yBs} stroke={C.col} strokeWidth="1.8" />);
          for (let k = 0; k < 4; k++) parts.push(<line key={"lh" + k} x1={x - 9 + k * 6} x2={x - 4 + k * 6} y1={yBs} y2={yBs + 5} stroke={C.col} strokeWidth="1" />);
        }
        return <g key={i}>{parts}</g>;
      })}

      {/* 보 */}
      <rect x={sx(0)} y={yB} width={sx(totalL) - sx(0)} height={beamH} fill={C.ink} rx="1" />

      {/* 핀 지점 (하부기둥이 없는 지점) */}
      {res.colInfo.map((ci, i) => {
        if (ci.low) return null;
        const x = sx(junctionXg[i]);
        const yT = yB + beamH, yBse = yT + 13;
        return (
          <g key={"p" + i}>
            <polygon points={`${x},${yT} ${x - 8},${yBse} ${x + 8},${yBse}`} fill="#fff" stroke={C.ink} strokeWidth="1.5" />
            <line x1={x - 11} x2={x + 11} y1={yBse} y2={yBse} stroke={C.ink} strokeWidth="1.5" />
            {[-8, -2, 4].map(o => <line key={o} x1={x + o} x2={x + o + 5} y1={yBse + 6} y2={yBse} stroke={C.ink} strokeWidth="1" />)}
          </g>
        );
      })}

      {/* 하중 */}
      {segs.map(s => s.loads.map((ld, li) => drawLoad(s, ld, li)))}

      {/* 지점 번호 + 반력 */}
      {junctionXg.map((xj, i) => (
        <g key={"j" + i}>
          <text x={sx(xj)} y={yB + 66} textAnchor="middle" className="jbadge" fill={C.ink}>{CIRC[i] || i + 1}</text>
          <text x={sx(xj)} y={yB + 80} textAnchor="middle" className="rlabel" fill={C.sub}
            stroke="#fff" strokeWidth="2.5" paintOrder="stroke">R={fmt(reactions[i], 1)}</text>
        </g>
      ))}

      {/* 치수선 */}
      <line x1={sx(0)} x2={sx(totalL)} y1={dimY} y2={dimY} stroke={C.sub} strokeWidth="1" />
      {nodeX.map((xn, i) => (
        <line key={i} x1={sx(xn)} x2={sx(xn)} y1={dimY - 5} y2={dimY + 5} stroke={C.sub} strokeWidth="1" />
      ))}
      {segs.map((s, i) => (
        <text key={i} x={sx(s.x0 + s.L / 2)} y={dimY - 4} textAnchor="middle" className="dimlbl" fill={C.sub}>
          {fmt(s.L, 1)}{i === segs.length - 1 ? " m" : ""}
        </text>
      ))}

      {hoverX != null && (
        <line x1={sx(hoverX)} x2={sx(hoverX)} y1={20} y2={dimY - 8} stroke={C.ink} strokeWidth="1" strokeDasharray="2 3" opacity="0.7" />
      )}
    </svg>
  );
}

/* ---------------- 강성행렬 패널 ---------------- */

function MatrixPanel({ res }) {
  const [open, setOpen] = useState(false);
  const n = res.dofLabels.length;
  return (
    <div className="card matcard">
      <button className="togbtn" onClick={() => setOpen(o => !o)}>
        {open ? "▾" : "▸"} 강성행렬 K · 하중벡터 F · 변위벡터 d 보기 <span className="mono sub">({n}×{n}, v=0 경계조건 적용 후)</span>
      </button>
      {open && (
        <div className="matwrap">
          <div className="dofchips">
            {res.dofLabels.map((lb, i) => <span key={i} className="dofchip mono">d{i + 1} = {lb}</span>)}
          </div>
          <div className="mattbl">
            <table className="tbl mono">
              <thead>
                <tr>
                  <th>K</th>
                  {res.dofLabels.map((_, j) => <th key={j}>d{j + 1}</th>)}
                  <th className="sep">F</th>
                  <th className="sep">d (해)</th>
                </tr>
              </thead>
              <tbody>
                {res.Kff.map((row, i) => (
                  <tr key={i}>
                    <th>d{i + 1}</th>
                    {row.map((v, j) => <td key={j}>{v === 0 ? "0" : v.toExponential(2)}</td>)}
                    <td className="sep">{res.Ff[i] === 0 ? "0" : res.Ff[i].toExponential(2)}</td>
                    <td className="sep">{res.df[i].toExponential(3)}</td>
                  </tr>
                ))}
              </tbody>
            </table>
          </div>
          <p className="foot">
            요소 강성행렬 k = EI/L³ · [[12, 6L, −12, 6L], [6L, 4L², −6L, 2L²], [−12, −6L, 12, −6L], [6L, 2L², −6L, 4L²]] 를 조합하고,
            기둥은 지점 회전자유도에 스프링 강성 Σ(4EI_c/H)로 기여합니다. 단위: 힘 kN, 길이 m, 모멘트 kN·m, 회전 rad.
          </p>
        </div>
      )}
    </div>
  );
}

/* ---------------- 인쇄용 해석조건 요약 ---------------- */

function loadText(ld, L) {
  switch (ld.type) {
    case "udl": return `등분포 w=${fmt(ld.w, 1)}`;
    case "point": return `집중 P=${fmt(ld.P, 1)} @${fmt(ld.a, 2)}m`;
    case "pointCenter": return `집중 P=${fmt(ld.P, 1)} @중앙`;
    case "triAsc": return `삼각형(우측 최대) w=${fmt(ld.w, 1)}`;
    case "triDesc": return `삼각형(좌측 최대) w=${fmt(ld.w, 1)}`;
    case "triSym": return `삼각형(중앙 최대) w=${fmt(ld.w, 1)}`;
    case "triN": return `삼각형 ${Math.round(ld.n ?? 2)}개(등간격) w=${fmt(ld.w, 1)}`;
    case "triValley": return `삼각형(양단 최대) w=${fmt(ld.w, 1)}`;
    case "partUdl": return `부분등분포 w=${fmt(ld.w, 1)} [${fmt(ld.a ?? 0, 2)}~${fmt(ld.b ?? L, 2)}m]`;
    case "trap": return `사다리꼴 w=${fmt(ld.w1 ?? ld.w, 1)}→${fmt(ld.w2 ?? ld.w, 1)} [${fmt(ld.a ?? 0, 2)}~${fmt(ld.b ?? L, 2)}m]`;
    case "trapSym": return `사다리꼴(슬래브형) w=${fmt(ld.w, 1)}, s=${fmt(ld.s ?? L / 4, 2)}m`;
    default: return ld.type;
  }
}

function InputSummary({ model, res }) {
  const segName = s => (s.kind === "cantL" ? "캔틸레버(좌)" : s.kind === "cantR" ? "캔틸레버(우)" : `스팬 ${s.idx + 1}`);
  const colTxt = c => (c && c.on ? `H=${fmt(c.H, 2)}m, ${c.b}×${c.h}` : "−");
  const today = new Date().toLocaleDateString("ko-KR");
  return (
    <div className="card printonly">
      <h3>해석 조건 요약</h3>
      <p className="foot" style={{ margin: "0 0 7px" }}>
        E = {fmt(model.E, 0)} MPa · 자중 {model.selfWeight ? `자동 포함 (γ=${model.gamma} kN/m³)` : "미포함"} · 해석: 직접강성법 (지점 v=0, 기둥 원단 고정) · 출력일 {today}
      </p>
      <table className="tbl">
        <thead><tr><th>부재</th><th>L (m)</th><th>단면 b×h (mm)</th><th style={{ textAlign: "left" }}>하중 (w: kN/m, P: kN)</th></tr></thead>
        <tbody>
          {res.segs.map((s, i) => (
            <tr key={i}>
              <td>{segName(s)}</td>
              <td className="mono">{fmt(s.L, 2)}</td>
              <td className="mono">{s.b}×{s.h}</td>
              <td className="mono" style={{ textAlign: "left" }}>{s.loads.filter(l => !l.self).map(l => loadText(l, s.L)).join(" ; ") || "−"}</td>
            </tr>
          ))}
        </tbody>
      </table>
      <table className="tbl" style={{ marginTop: 7 }}>
        <thead><tr><th>지점</th><th>하부기둥</th><th>상부기둥</th><th>지점 조건</th></tr></thead>
        <tbody>
          {model.supports.map((sp, i) => (
            <tr key={i}>
              <td>{CIRC[i] || i + 1}</td>
              <td className="mono">{colTxt(sp.low)}</td>
              <td className="mono">{colTxt(sp.up)}</td>
              <td>{sp.low.on || sp.up.on ? "기둥 접합" : "핀"}</td>
            </tr>
          ))}
        </tbody>
      </table>
    </div>
  );
}

/* ---------------- A4 PDF 생성 엔진 ----------------
   샌드박스 환경에서 window.print()가 차단되므로, 캔버스에 보고서를 조판하고
   페이지별 JPEG을 PDF 바이너리(DCTDecode XObject)로 직접 조립하여 다운로드한다. */

const PDF_PAGE_W = 794, PDF_PAGE_H = 1123, PDF_SCALE = 2, PDF_M = 45; // A4 @96dpi, 여백 12mm
const PDF_SANS = "'IBM Plex Sans KR','Malgun Gothic','Apple SD Gothic Neo',sans-serif";
const PDF_MONO = "'IBM Plex Mono',ui-monospace,Consolas,monospace";

const SVG_EMBED_CSS = `
text{font-family:'Malgun Gothic','Apple SD Gothic Neo','Noto Sans KR',sans-serif;}
.ptitle{font-size:11.5px;font-weight:700;letter-spacing:.04em;}
.pzero,.rlabel{font-size:9.5px;font-family:ui-monospace,Consolas,monospace;}
.plabel{font-size:10.5px;font-weight:600;font-family:ui-monospace,Consolas,monospace;}
.loadlbl{font-size:10px;font-weight:600;font-family:ui-monospace,Consolas,monospace;}
.jbadge{font-size:13px;}
.dimlbl{font-size:10px;font-family:ui-monospace,Consolas,monospace;}
.xaxis text{font-size:9.5px;font-family:ui-monospace,Consolas,monospace;}
.preadout{display:none;}
`;

async function svgToImg(svgEl) {
  const clone = svgEl.cloneNode(true);
  clone.setAttribute("xmlns", "http://www.w3.org/2000/svg");
  const st = document.createElementNS("http://www.w3.org/2000/svg", "style");
  st.textContent = SVG_EMBED_CSS;
  clone.insertBefore(st, clone.firstChild);
  const xml = new XMLSerializer().serializeToString(clone);
  const img = new Image();
  await new Promise((resolve, reject) => {
    img.onload = resolve;
    img.onerror = () => reject(new Error("SVG 래스터화 실패"));
    img.src = "data:image/svg+xml;charset=utf-8," + encodeURIComponent(xml);
  });
  return { img, w: parseFloat(svgEl.getAttribute("width")), h: parseFloat(svgEl.getAttribute("height")) };
}

function pdfPager() {
  const pages = [];
  const st = { ctx: null, y: 0 };
  const newPage = () => {
    const cv = document.createElement("canvas");
    cv.width = PDF_PAGE_W * PDF_SCALE;
    cv.height = PDF_PAGE_H * PDF_SCALE;
    const ctx = cv.getContext("2d");
    ctx.scale(PDF_SCALE, PDF_SCALE);
    ctx.fillStyle = "#FFFFFF";
    ctx.fillRect(0, 0, PDF_PAGE_W, PDF_PAGE_H);
    ctx.imageSmoothingEnabled = true;
    ctx.imageSmoothingQuality = "high";
    pages.push(cv);
    st.ctx = ctx;
    st.y = PDF_M;
  };
  newPage();
  const ensure = h => { if (st.y + h > PDF_PAGE_H - PDF_M) { newPage(); return true; } return false; };
  return { st, ensure, pages, cw: PDF_PAGE_W - 2 * PDF_M };
}

function pdfWrap(ctx, text, maxW) {
  const out = [];
  let line = "";
  for (const ch of text) {
    if (ch === "\n") { out.push(line); line = ""; continue; }
    const t = line + ch;
    if (ctx.measureText(t).width > maxW && line) { out.push(line); line = ch === " " ? "" : ch; }
    else line = t;
  }
  if (line) out.push(line);
  return out;
}

function pdfTable(P, { title, headers, rows, widths, aligns, monoCols = [] }) {
  const { st, ensure, cw } = P;
  const rowH = 19, padX = 6;
  const xs = [PDF_M];
  widths.forEach(f => xs.push(xs[xs.length - 1] + f * cw));
  const drawRow = (cells, head) => {
    if (ensure(rowH + 2) && !head) drawRow(headers, true); // 페이지 넘어가면 머리행 반복
    const ctx = st.ctx, yy = st.y;
    if (head) { ctx.fillStyle = "#F1F3EF"; ctx.fillRect(PDF_M, yy, cw, rowH); }
    ctx.strokeStyle = "#C2C9C0";
    ctx.lineWidth = 0.7;
    for (let i = 0; i < cells.length; i++) ctx.strokeRect(xs[i], yy, xs[i + 1] - xs[i], rowH);
    ctx.fillStyle = head ? "#5C6B66" : "#1C2B33";
    ctx.textBaseline = "middle";
    for (let i = 0; i < cells.length; i++) {
      const al = head ? "center" : (aligns && aligns[i]) || "right";
      ctx.font = head ? `600 10px ${PDF_SANS}` : monoCols.includes(i) ? `10.5px ${PDF_MONO}` : `10.5px ${PDF_SANS}`;
      ctx.textAlign = al;
      const tx = al === "left" ? xs[i] + padX : al === "center" ? (xs[i] + xs[i + 1]) / 2 : xs[i + 1] - padX;
      ctx.fillText(String(cells[i]), tx, yy + rowH / 2 + 0.5, xs[i + 1] - xs[i] - 2 * padX);
    }
    st.y += rowH;
  };
  if (title) {
    ensure(20 + rowH * 2);
    const ctx = st.ctx;
    ctx.font = `700 12px ${PDF_SANS}`;
    ctx.fillStyle = "#1C2B33";
    ctx.textAlign = "left";
    ctx.textBaseline = "alphabetic";
    ctx.fillText(title, PDF_M, st.y + 12);
    st.y += 20;
  }
  drawRow(headers, true);
  rows.forEach(r => drawRow(r, false));
  st.y += 12;
}

function pdfNote(P, text) {
  P.ensure(16);
  const ctx = P.st.ctx;
  ctx.font = `9.5px ${PDF_MONO}`;
  ctx.fillStyle = "#5C6B66";
  ctx.textAlign = "left";
  ctx.textBaseline = "alphabetic";
  ctx.fillText(text, PDF_M, P.st.y + 9);
  P.st.y += 18;
}

function pdfTitleBlock(P, derived) {
  const { st, cw } = P;
  const ctx = st.ctx, h = 62;
  ctx.strokeStyle = "#1C2B33";
  ctx.lineWidth = 1.4;
  ctx.strokeRect(PDF_M, st.y, cw, h);
  ctx.strokeStyle = "#B9BFB8";
  ctx.lineWidth = 0.7;
  ctx.strokeRect(PDF_M + 3, st.y + 3, cw - 6, h - 6);
  ctx.textAlign = "left";
  ctx.textBaseline = "alphabetic";
  ctx.fillStyle = "#1C2B33";
  ctx.font = `700 17px ${PDF_SANS}`;
  ctx.fillText("SUB-BEAM 2D — 해석 결과 보고서", PDF_M + 14, st.y + 26);
  ctx.font = `11px ${PDF_SANS}`;
  ctx.fillStyle = "#5C6B66";
  ctx.fillText("연속보 · 부분골조 해석 (직접강성법) — 휨모멘트 · 전단력 · 처짐", PDF_M + 14, st.y + 45);
  ctx.textAlign = "right";
  ctx.font = `10.5px ${PDF_MONO}`;
  ctx.fillStyle = "#1C2B33";
  ctx.fillText(`M⁺max ${fmt(derived.Mmax.val)} · M⁻max ${fmt(derived.Mmin.val)} kN·m`, PDF_M + cw - 14, st.y + 26);
  ctx.fillText(`|V|max ${fmt(Math.abs(derived.Vmax.val))} kN · δmax ${fmt(Math.abs(derived.Dmax.val * 1000), 2)} mm · ${new Date().toLocaleDateString("ko-KR")}`, PDF_M + cw - 14, st.y + 45);
  st.y += h + 14;
}

function pdfFromJpegPages(jpegs) {
  const W = 595.28, H = 841.89; // A4 pt
  const enc = new TextEncoder();
  const parts = [];
  let offset = 0;
  const offsets = [];
  const push = data => {
    const b = typeof data === "string" ? enc.encode(data) : data;
    parts.push(b);
    offset += b.length;
  };
  push("%PDF-1.4\n");
  push(new Uint8Array([0x25, 0xe2, 0xe3, 0xcf, 0xd3, 0x0a]));
  const n = jpegs.length;
  const pageNum = i => 3 + i * 3, contNum = i => 4 + i * 3, imgNum = i => 5 + i * 3;
  const obj = (num, body) => { offsets[num] = offset; push(`${num} 0 obj\n${body}\nendobj\n`); };
  obj(1, "<< /Type /Catalog /Pages 2 0 R >>");
  obj(2, `<< /Type /Pages /Kids [${jpegs.map((_, i) => `${pageNum(i)} 0 R`).join(" ")}] /Count ${n} >>`);
  jpegs.forEach((jp, i) => {
    const content = `q ${W} 0 0 ${H} 0 0 cm /Im0 Do Q`;
    obj(pageNum(i), `<< /Type /Page /Parent 2 0 R /MediaBox [0 0 ${W} ${H}] /Resources << /XObject << /Im0 ${imgNum(i)} 0 R >> /ProcSet [/PDF /ImageC] >> /Contents ${contNum(i)} 0 R >>`);
    obj(contNum(i), `<< /Length ${content.length} >>\nstream\n${content}\nendstream`);
    offsets[imgNum(i)] = offset;
    push(`${imgNum(i)} 0 obj\n<< /Type /XObject /Subtype /Image /Width ${jp.w} /Height ${jp.h} /ColorSpace /DeviceRGB /BitsPerComponent 8 /Filter /DCTDecode /Length ${jp.bytes.length} >>\nstream\n`);
    push(jp.bytes);
    push("\nendstream\nendobj\n");
  });
  const xref = offset;
  const count = 3 + n * 3;
  push(`xref\n0 ${count}\n0000000000 65535 f \n`);
  for (let i = 1; i < count; i++) push(`${String(offsets[i]).padStart(10, "0")} 00000 n \n`);
  push(`trailer\n<< /Size ${count} /Root 1 0 R >>\nstartxref\n${xref}\n%%EOF`);
  return new Blob(parts, { type: "application/pdf" });
}

async function buildPdfReport(model, res, derived, sheetEl) {
  try { if (document.fonts && document.fonts.ready) await document.fonts.ready; } catch (e) { /* 무시 */ }
  const P = pdfPager();
  const segName = s => (s.kind === "cantL" ? "캔틸레버(좌)" : s.kind === "cantR" ? "캔틸레버(우)" : `스팬 ${s.idx + 1}`);

  pdfTitleBlock(P, derived);

  pdfTable(P, {
    title: `해석 조건 요약 — E=${fmt(model.E, 0)} MPa · 자중 ${model.selfWeight ? `포함(γ=${model.gamma})` : "미포함"} · 지점 v=0 · 기둥 원단 고정`,
    headers: ["부재", "L (m)", "단면 b×h", "하중 (w: kN/m, P: kN)"],
    widths: [0.13, 0.09, 0.14, 0.64],
    aligns: ["center", "right", "center", "left"],
    monoCols: [1, 2, 3],
    rows: res.segs.map(s => [segName(s), fmt(s.L, 2), `${s.b}×${s.h}`,
      s.loads.filter(l => !l.self).map(l => loadText(l, s.L)).join(" ; ") || "−"]),
  });
  pdfTable(P, {
    headers: ["지점", "하부기둥", "상부기둥", "지점 조건"],
    widths: [0.12, 0.34, 0.34, 0.2],
    aligns: ["center", "center", "center", "center"],
    monoCols: [1, 2],
    rows: model.supports.map((sp, i) => [CIRC[i] || i + 1,
      sp.low.on ? `H=${fmt(sp.low.H, 2)}m, ${sp.low.b}×${sp.low.h}` : "−",
      sp.up.on ? `H=${fmt(sp.up.H, 2)}m, ${sp.up.b}×${sp.up.h}` : "−",
      sp.low.on || sp.up.on ? "기둥 접합" : "핀"]),
  });

  /* 다이어그램 4종 (A4 폭 700px 렌더 상태에서 벡터 → 2배 래스터) */
  const svgs = Array.from(sheetEl.querySelectorAll("svg.plot"));
  for (const el of svgs) {
    const { img, w, h } = await svgToImg(el);
    const dh = h * P.cw / w;
    P.ensure(dh + 4);
    P.st.ctx.drawImage(img, PDF_M, P.st.y, P.cw, dh);
    P.st.y += dh + 4;
  }
  P.st.y += 8;

  pdfTable(P, {
    title: "지점 반력 · 절점 회전각",
    headers: ["지점", "x (m)", "R (kN)", "θ (×10⁻³ rad)"],
    widths: [0.16, 0.28, 0.28, 0.28],
    aligns: ["center", "right", "right", "right"],
    monoCols: [1, 2, 3],
    rows: res.reactions.map((R, i) => [CIRC[i] || i + 1, fmt(res.junctionXg[i], 2), fmt(R, 2),
      fmt(res.d[2 * res.junctionNodes[i] + 1] * 1000, 3)]),
  });
  pdfNote(P, `평형 검토: ΣR = ${fmt(res.sumR, 2)} kN, Σ하중 = ${fmt(res.totalLoad, 2)} kN, 오차 = ${(res.sumR - res.totalLoad).toExponential(1)} kN`);

  pdfTable(P, {
    title: "부재 단부력 및 최대값 (M: kN·m, V: kN)",
    headers: ["부재", "L (m)", "M좌단", "M우단", "M⁺max (위치)", "V좌단", "V우단", "δmax (mm)"],
    widths: [0.14, 0.08, 0.11, 0.11, 0.23, 0.11, 0.11, 0.11],
    aligns: ["center", "right", "right", "right", "right", "right", "right", "right"],
    monoCols: [1, 2, 3, 4, 5, 6, 7],
    rows: res.segs.map(s => {
      const p0 = s.diagram[0], p1 = s.diagram[s.diagram.length - 1];
      let mx = p0, dm = p0;
      s.diagram.forEach(p => { if (p.M > mx.M) mx = p; if (Math.abs(p.defl) > Math.abs(dm.defl)) dm = p; });
      return [segName(s), fmt(s.L, 2), fmt(p0.M, 1), fmt(p1.M, 1),
        mx.M > 0.05 ? `${fmt(mx.M, 1)} (x=${fmt(mx.x, 2)})` : "−",
        fmt(p0.V, 1), fmt(p1.V, 1),
        `${fmt(Math.abs(dm.defl * 1000), 2)}${dm.defl < -1e-9 ? "↓" : dm.defl > 1e-9 ? "↑" : ""}`];
    }),
  });

  const colRows = res.colInfo.flatMap((ci, i) => ["low", "up"].filter(k => ci[k]).map(k =>
    [CIRC[i] || i + 1, k === "low" ? "하부" : "상부", fmt(ci[k].H, 2), `${ci[k].b}×${ci[k].h}`,
      fmt(ci[k].Mnear, 2), fmt(ci[k].Mfar, 2), fmt(ci[k].V, 2)]));
  if (colRows.length) {
    pdfTable(P, {
      title: "기둥 단부모멘트 (원단 고정, 이월률 1/2)",
      headers: ["지점", "구분", "H (m)", "단면", "M절점측 (kN·m)", "M원단측 (kN·m)", "기둥전단 (kN)"],
      widths: [0.1, 0.1, 0.11, 0.15, 0.2, 0.2, 0.14],
      aligns: ["center", "center", "right", "center", "right", "right", "right"],
      monoCols: [2, 3, 4, 5, 6],
      rows: colRows,
    });
  }

  /* 가정 및 부호 규약 */
  {
    P.ensure(80);
    let ctx = P.st.ctx;
    ctx.font = `700 12px ${PDF_SANS}`;
    ctx.fillStyle = "#1C2B33";
    ctx.textAlign = "left";
    ctx.textBaseline = "alphabetic";
    ctx.fillText("가정 및 부호 규약", PDF_M, P.st.y + 12);
    P.st.y += 20;
    const notes = [
      "모든 지점은 수직변위 구속(v=0), 골조는 비횡변위(수평변위 무시)로 가정합니다. 기둥은 원단 고정으로 절점에 회전강성 4EI/H를 제공하며, 기둥이 없는 지점은 핀지점입니다. 부재는 등단면 Euler–Bernoulli 보로 전단·축변형은 무시하고, 하중은 하향(+)으로 입력합니다.",
      "정모멘트(+)는 하부 인장이며 B.M.D는 인장측(아래)에 그립니다. 전단력(+)은 좌측부의 상향 합력, 처짐은 ↓가 하향입니다. 2방향 슬래브형 사다리꼴의 램프 s는 통상 단변 스팬의 1/2(Lx/2), 삼각형 n개(등간격)는 작은보 (n−1)개 배치 시의 하중 패턴입니다.",
      "검증: 단순보 wL²/8 · 2경간 −wL²/8 · 삼각형 wL²/(9√3) · 이중삼각형 wL²/16 · 캔틸레버 −wℓ²/2 · 고정단 −wL²/12 · 처짐 5wL⁴/384EI 등 이론해 84항목 일치",
    ];
    notes.forEach(t => {
      ctx = P.st.ctx;
      ctx.font = `9.8px ${PDF_SANS}`;
      ctx.fillStyle = "#3A4A52";
      pdfWrap(ctx, t, P.cw).forEach(ln => {
        P.ensure(14);
        P.st.ctx.font = `9.8px ${PDF_SANS}`;
        P.st.ctx.fillStyle = "#3A4A52";
        P.st.ctx.textAlign = "left";
        P.st.ctx.fillText(ln, PDF_M, P.st.y + 10);
        P.st.y += 14;
      });
      P.st.y += 4;
    });
  }

  /* 페이지 번호 */
  P.pages.forEach((cv, i) => {
    const ctx = cv.getContext("2d");
    ctx.font = `9px ${PDF_MONO}`;
    ctx.fillStyle = "#8A948E";
    ctx.textBaseline = "alphabetic";
    ctx.textAlign = "center";
    ctx.fillText(`${i + 1} / ${P.pages.length}`, PDF_PAGE_W / 2, PDF_PAGE_H - 18);
    ctx.textAlign = "left";
    ctx.fillText("SUB-BEAM 2D · 직접강성법 v1.0", PDF_M, PDF_PAGE_H - 18);
    ctx.textAlign = "right";
    ctx.fillText("Made by KSN", PDF_PAGE_W - PDF_M, PDF_PAGE_H - 18);
  });

  /* JPEG 변환 → PDF 조립 → 다운로드 */
  const jpegs = P.pages.map(cv => {
    const b64 = cv.toDataURL("image/jpeg", 0.92).split(",")[1];
    const bin = atob(b64);
    const bytes = new Uint8Array(bin.length);
    for (let i = 0; i < bin.length; i++) bytes[i] = bin.charCodeAt(i);
    return { bytes, w: cv.width, h: cv.height };
  });
  const blob = pdfFromJpegPages(jpegs);
  const url = URL.createObjectURL(blob);
  const a = document.createElement("a");
  a.href = url;
  a.download = `sub-beam-report_${new Date().toISOString().slice(0, 10)}.pdf`;
  document.body.appendChild(a);
  a.click();
  a.remove();
  setTimeout(() => URL.revokeObjectURL(url), 5000);
}

/* ---------------- 메인 ---------------- */

export default function SubBeamAnalyzer() {
  const [model, setModel] = useState(makeDefaultModel);
  const [hoverX, setHoverX] = useState(null);
  const sheetRef = useRef(null);
  const w = useWidth(sheetRef);
  const [printing, setPrinting] = useState(false);
  useEffect(() => {
    const before = () => setPrinting(true);
    const after = () => setPrinting(false);
    window.addEventListener("beforeprint", before);
    window.addEventListener("afterprint", after);
    return () => {
      window.removeEventListener("beforeprint", before);
      window.removeEventListener("afterprint", after);
    };
  }, []);
  const [pdfBusy, setPdfBusy] = useState(false);
  const generatePdf = () => {
    if (pdfBusy || res.error) return;
    setHoverX(null);
    setPrinting(true);   // 다이어그램을 A4 폭(700px) 기준으로 재렌더
    setPdfBusy(true);
    setTimeout(async () => {
      try {
        await buildPdfReport(model, res, derived, sheetRef.current);
      } catch (e) {
        console.error("PDF 생성 실패:", e);
      } finally {
        setPrinting(false);
        setPdfBusy(false);
      }
    }, 220);
  };
  const plotW = printing ? 700 : Math.max(320, w - 30);

  const set = fn => setModel(m => { const n = JSON.parse(JSON.stringify(m)); fn(n); return n; });

  const setSpanCount = nv => set(m => {
    const n = Math.max(1, Math.min(8, Math.round(nv)));
    while (m.spans.length < n) {
      const cp = JSON.parse(JSON.stringify(m.spans[m.spans.length - 1]));
      cp.loads.forEach(ld => { ld.id = uid(); });
      m.spans.push(cp);
    }
    m.spans.length = n;
    while (m.supports.length < n + 1) m.supports.push(JSON.parse(JSON.stringify(m.supports[m.supports.length - 1])));
    m.supports.length = n + 1;
  });

  const res = useMemo(() => {
    try { return analyze(model); }
    catch (e) { return { error: e.message || String(e) }; }
  }, [model]);

  /* 극값 라벨 + 요약 */
  const derived = useMemo(() => {
    if (res.error) return null;
    const bm = [], sf = [], df = [];
    const seenB = new Set(), seenS = new Set(), seenD = new Set();
    const push = (arr, seen, xg, val, tol) => {
      if (Math.abs(val) < tol) return;
      const key = Math.round(xg * 50) + "_" + Math.round(val * 5);
      if (seen.has(key)) return;
      seen.add(key);
      arr.push({ xg, val });
    };
    let Mmax = { val: -Infinity }, Mmin = { val: Infinity }, Vmax = { val: 0 }, Dmax = { val: 0 };
    res.segs.forEach(s => {
      let mx = s.diagram[0], mn = s.diagram[0], dm = s.diagram[0];
      s.diagram.forEach(p => {
        if (p.M > mx.M) mx = p;
        if (p.M < mn.M) mn = p;
        if (Math.abs(p.defl) > Math.abs(dm.defl)) dm = p;
        if (p.M > Mmax.val) Mmax = { val: p.M, xg: p.xg };
        if (p.M < Mmin.val) Mmin = { val: p.M, xg: p.xg };
        if (Math.abs(p.V) > Math.abs(Vmax.val)) Vmax = { val: p.V, xg: p.xg };
        if (Math.abs(p.defl) > Math.abs(Dmax.val)) Dmax = { val: p.defl, xg: p.xg };
      });
      push(bm, seenB, mx.xg, mx.M, 0.05);
      push(bm, seenB, mn.xg, mn.M, 0.05);
      push(sf, seenS, s.diagram[0].xg, s.diagram[0].V, 0.05);
      push(sf, seenS, s.diagram[s.diagram.length - 1].xg, s.diagram[s.diagram.length - 1].V, 0.05);
      push(df, seenD, dm.xg, dm.defl * 1000, 0.01);
    });
    const vpts = res.segs.flatMap(s => s.diagram.map(p => ({ xg: p.xg, val: p.V })));
    const mpts = res.segs.flatMap(s => s.diagram.map(p => ({ xg: p.xg, val: p.M })));
    const dpts = res.segs.flatMap(s => s.diagram.map(p => ({ xg: p.xg, val: p.defl * 1000 })));
    return { bm, sf, df, vpts, mpts, dpts, Mmax, Mmin, Vmax, Dmax };
  }, [res]);

  const segName = s => (s.kind === "cantL" ? "캔틸레버(좌)" : s.kind === "cantR" ? "캔틸레버(우)" : `스팬 ${s.idx + 1}`);
  const hasCols = !res.error && res.colInfo.some(ci => ci.low || ci.up);

  return (
    <div className="app">
      <style>{CSS}</style>

      <header className="tblock">
        <div>
          <div className="tb-title">SUB-BEAM 2D <span className="tb-ver mono">직접강성법 v1.0</span></div>
          <div className="tb-sub">연속보 · 부분골조(기둥 포함) 해석 — 휨모멘트 · 전단력 · 처짐</div>
        </div>
        {derived && (
          <div className="tb-vals mono">
            <div className="chip"><span className="ck">M⁺max</span><b style={{ color: C.moment }}>{fmt(derived.Mmax.val)}</b><span className="cu">kN·m</span></div>
            <div className="chip"><span className="ck">M⁻max</span><b style={{ color: C.moment }}>{fmt(derived.Mmin.val)}</b><span className="cu">kN·m</span></div>
            <div className="chip"><span className="ck">|V|max</span><b style={{ color: C.shear }}>{fmt(Math.abs(derived.Vmax.val))}</b><span className="cu">kN</span></div>
            <div className="chip"><span className="ck">δmax</span><b style={{ color: C.defl }}>{fmt(Math.abs(derived.Dmax.val * 1000), 2)}</b><span className="cu">mm</span></div>
          </div>
        )}
        <button className="printbtn" onClick={generatePdf} disabled={pdfBusy}
          title="A4 규격 PDF 파일을 생성하여 다운로드합니다">{pdfBusy ? "PDF 생성 중…" : "PDF 다운로드 (A4)"}</button>
      </header>

      <div className="grid">
        {/* ---------- 입력 레일 ---------- */}
        <aside className="rail">
          <div className="card">
            <div className="cardhead"><h3>해석 조건</h3>
              <button className="resetbtn" onClick={() => setModel(makeDefaultModel())}>예제로 초기화</button>
            </div>
            <div className="row">
              <Num label="스팬 수" value={model.spans.length} onChange={setSpanCount} step={1} min={1} width={56} />
              <Num label="E" value={model.E} onChange={v => set(m => { m.E = v; })} unit="MPa" step={500} min={100} width={80} />
            </div>
            <p className="hint mono">C24≈25,000 · C30≈27,500 · SM355≈205,000</p>
            <div className="row">
              <Chk label="자중 자동 포함" checked={model.selfWeight} onChange={v => set(m => { m.selfWeight = v; })} />
              {model.selfWeight && <Num label="γ" value={model.gamma} onChange={v => set(m => { m.gamma = v; })} unit="kN/m³" step={0.5} min={1} width={56} />}
            </div>
          </div>

          {model.spans.map((s, i) => (
            <div className="card" key={i}>
              <div className="cardhead"><h3>스팬 {i + 1} <span className="sub">보</span></h3>
                <button className="minibtn" onClick={() => set(m => { m.spans.forEach(sp => { sp.b = s.b; sp.h = s.h; }); })}>단면 전체 적용</button>
              </div>
              <div className="row">
                <Num label="L" value={s.L} onChange={v => set(m => { m.spans[i].L = v; })} unit="m" step={0.1} min={0.1} width={62} />
                <Num label="b" value={s.b} onChange={v => set(m => { m.spans[i].b = v; })} unit="mm" step={10} min={50} width={62} />
                <Num label="h" value={s.h} onChange={v => set(m => { m.spans[i].h = v; })} unit="mm" step={10} min={50} width={62} />
              </div>
              <LoadsEditor loads={s.loads} segL={s.L} onChange={ls => set(m => { m.spans[i].loads = ls; })} />
            </div>
          ))}

          <div className="card">
            <div className="cardhead"><h3>지점 · 기둥</h3>
              <button className="minibtn" onClick={() => set(m => {
                const src = JSON.parse(JSON.stringify(m.supports[0]));
                m.supports = m.supports.map(() => JSON.parse(JSON.stringify(src)));
              })}>지점① 전체 적용</button>
            </div>
            {model.supports.map((sp, i) => (
              <div className="suprow" key={i}>
                <div className="supname mono">{CIRC[i] || i + 1}</div>
                <div className="supcols">
                  {["low", "up"].map(key => (
                    <div className="colline" key={key}>
                      <Chk label={key === "low" ? "하부기둥" : "상부기둥"} checked={sp[key].on}
                        onChange={v => set(m => { m.supports[i][key].on = v; })} />
                      {sp[key].on && (<>
                        <Num label="H" value={sp[key].H} onChange={v => set(m => { m.supports[i][key].H = v; })} unit="m" step={0.1} min={0.2} width={52} />
                        <Num value={sp[key].b} onChange={v => set(m => { m.supports[i][key].b = v; })} step={10} min={50} width={54} />
                        <span className="nu">×</span>
                        <Num value={sp[key].h} onChange={v => set(m => { m.supports[i][key].h = v; })} unit="mm" step={10} min={50} width={54} />
                      </>)}
                    </div>
                  ))}
                </div>
              </div>
            ))}
            <p className="hint">기둥이 없는 지점은 핀(단순)지점으로 처리합니다. 기둥 원단은 고정입니다.</p>
          </div>

          <div className="card">
            <div className="cardhead"><h3>캔틸레버</h3></div>
            {["cantL", "cantR"].map(key => (
              <div key={key} className="cantblock">
                <Chk label={key === "cantL" ? "좌측 캔틸레버" : "우측 캔틸레버"} checked={model[key].on}
                  onChange={v => set(m => { m[key].on = v; })} />
                {model[key].on && (<>
                  <div className="row">
                    <Num label="ℓ" value={model[key].L} onChange={v => set(m => { m[key].L = v; })} unit="m" step={0.1} min={0.1} width={58} />
                    <Num label="b" value={model[key].b} onChange={v => set(m => { m[key].b = v; })} unit="mm" step={10} min={50} width={58} />
                    <Num label="h" value={model[key].h} onChange={v => set(m => { m[key].h = v; })} unit="mm" step={10} min={50} width={58} />
                  </div>
                  <LoadsEditor loads={model[key].loads} segL={model[key].L} onChange={ls => set(m => { m[key].loads = ls; })} />
                </>)}
              </div>
            ))}
          </div>
        </aside>

        {/* ---------- 해석 시트 ---------- */}
        <main className="sheet" ref={sheetRef}>
          {res.error ? (
            <div className="card errbox">해석 불가: {res.error}</div>
          ) : (
            <>
              <InputSummary model={model} res={res} />
              <div className="card plotcard">
                <ModelView res={res} model={model} w={plotW} hoverX={hoverX} setHoverX={setHoverX} />
                <DiagramPlot title="전단력도 S.F.D" unit="kN" color={C.shear} pts={derived.vpts} labels={derived.sf}
                  invert={false} height={150} w={plotW} totalL={res.totalL} junctionXg={res.junctionXg}
                  hoverX={hoverX} setHoverX={setHoverX} />
                <DiagramPlot title="휨모멘트도 B.M.D (인장측 표시)" unit="kN·m" color={C.moment} pts={derived.mpts} labels={derived.bm}
                  invert={true} height={176} w={plotW} totalL={res.totalL} junctionXg={res.junctionXg}
                  hoverX={hoverX} setHoverX={setHoverX} />
                <DiagramPlot title="처짐도" unit="mm" color={C.defl} pts={derived.dpts} labels={derived.df}
                  invert={false} height={124} w={plotW} totalL={res.totalL} junctionXg={res.junctionXg}
                  hoverX={hoverX} setHoverX={setHoverX} showXAxis dec={2} deflMode />
              </div>

              <div className="card">
                <h3>지점 반력 · 절점 회전각</h3>
                <table className="tbl">
                  <thead><tr><th>지점</th><th>x (m)</th><th>R (kN)</th><th>θ (×10⁻³ rad)</th></tr></thead>
                  <tbody>
                    {res.reactions.map((R, i) => (
                      <tr key={i}>
                        <td>{CIRC[i] || i + 1}</td>
                        <td className="mono">{fmt(res.junctionXg[i], 2)}</td>
                        <td className="mono">{fmt(R, 2)}</td>
                        <td className="mono">{fmt(res.d[2 * res.junctionNodes[i] + 1] * 1000, 3)}</td>
                      </tr>
                    ))}
                  </tbody>
                </table>
                <p className="foot mono">평형 검토: ΣR = {fmt(res.sumR, 2)} kN, Σ하중 = {fmt(res.totalLoad, 2)} kN, 오차 = {(res.sumR - res.totalLoad).toExponential(1)} kN</p>
              </div>

              <div className="card">
                <h3>부재 단부력 및 최대값</h3>
                <table className="tbl">
                  <thead><tr>
                    <th>부재</th><th>L (m)</th><th>M좌단</th><th>M우단</th><th>M⁺max (위치)</th><th>V좌단</th><th>V우단</th><th>δmax (mm)</th>
                  </tr></thead>
                  <tbody>
                    {res.segs.map((s, i) => {
                      const p0 = s.diagram[0], p1 = s.diagram[s.diagram.length - 1];
                      let mx = p0, dm = p0;
                      s.diagram.forEach(p => { if (p.M > mx.M) mx = p; if (Math.abs(p.defl) > Math.abs(dm.defl)) dm = p; });
                      return (
                        <tr key={i}>
                          <td>{segName(s)}</td>
                          <td className="mono">{fmt(s.L, 2)}</td>
                          <td className="mono">{fmt(p0.M, 1)}</td>
                          <td className="mono">{fmt(p1.M, 1)}</td>
                          <td className="mono">{mx.M > 0.05 ? `${fmt(mx.M, 1)} (x=${fmt(mx.x, 2)})` : "–"}</td>
                          <td className="mono">{fmt(p0.V, 1)}</td>
                          <td className="mono">{fmt(p1.V, 1)}</td>
                          <td className="mono">{fmt(Math.abs(dm.defl * 1000), 2)}{dm.defl < -1e-9 ? "↓" : dm.defl > 1e-9 ? "↑" : ""}</td>
                        </tr>
                      );
                    })}
                  </tbody>
                </table>
                <p className="foot">M 단위 kN·m, V 단위 kN. 좌단/우단은 각 부재의 왼쪽/오른쪽 끝 단면입니다.</p>
              </div>

              {hasCols && (
                <div className="card">
                  <h3>기둥 단부모멘트 <span className="sub">(원단 고정, 이월률 1/2)</span></h3>
                  <table className="tbl">
                    <thead><tr>
                      <th>지점</th><th>구분</th><th>H (m)</th><th>단면 (mm)</th><th>M절점측 (kN·m)</th><th>M원단측 (kN·m)</th><th>기둥전단 (kN)</th>
                    </tr></thead>
                    <tbody>
                      {res.colInfo.flatMap((ci, i) =>
                        ["low", "up"].filter(k => ci[k]).map(k => (
                          <tr key={i + k}>
                            <td>{CIRC[i] || i + 1}</td>
                            <td>{k === "low" ? "하부기둥" : "상부기둥"}</td>
                            <td className="mono">{fmt(ci[k].H, 2)}</td>
                            <td className="mono">{ci[k].b}×{ci[k].h}</td>
                            <td className="mono">{fmt(ci[k].Mnear, 2)}</td>
                            <td className="mono">{fmt(ci[k].Mfar, 2)}</td>
                            <td className="mono">{fmt(ci[k].V, 2)}</td>
                          </tr>
                        ))
                      )}
                    </tbody>
                  </table>
                  <p className="foot">부호는 절점 회전각 θ(반시계+) 기준의 부재단 모멘트입니다. 절점에서 보 단부모멘트와 기둥 모멘트 합은 평형을 이룹니다.</p>
                </div>
              )}

              <MatrixPanel res={res} />

              <div className="card notes">
                <h3>가정 및 부호 규약</h3>
                <p>모든 지점은 수직변위 구속(v=0), 골조는 비횡변위(수평변위 무시)로 가정합니다. 기둥은 원단 고정으로 절점에 회전강성 4EI/H를 제공하며, 기둥이 없는 지점은 핀지점입니다. 부재는 등단면 Euler–Bernoulli 보로 전단변형과 축변형은 무시하고, 하중은 하향(+)으로 입력합니다.</p>
                <p>정모멘트(+)는 하부 인장이며 B.M.D는 인장측(아래)에 그립니다. 전단력(+)은 좌측부의 상향 합력, 처짐은 ↓가 하향입니다. 2방향 슬래브형 사다리꼴의 램프 길이 s는 통상 단변 스팬의 1/2(Lx/2)을 사용합니다. 삼각형 n개(등간격 연속)는 큰보 스팬을 n등분하는 작은보 (n−1)개 배치 시의 슬래브 하중 패턴이며(n=2: 중앙 작은보 1개), 작은보 반력은 집중하중으로 별도 추가하세요.</p>
                <p className="mono sub">검증: 단순보 wL²/8 · 2경간 연속보 −wL²/8 · 삼각형 wL²/(9√3) · 이중삼각형 wL²/16 · 캔틸레버 −wℓ²/2 · 고정단 −wL²/12 · 처짐 5wL⁴/384EI · 부분/사다리꼴 정역학·중첩해 등 이론해 84항목 일치</p>
              </div>
            </>
          )}
        </main>
      </div>
      <div className="madeby">Made by KSN</div>
    </div>
  );
}

/* ---------------- 스타일 ---------------- */

const CSS = `
@import url('https://fonts.googleapis.com/css2?family=IBM+Plex+Sans+KR:wght@400;500;700&family=IBM+Plex+Mono:wght@400;500&display=swap');
:root { color-scheme: light; }
.app {
  --sans: 'IBM Plex Sans KR','Pretendard','Apple SD Gothic Neo','Malgun Gothic',system-ui,sans-serif;
  --mono: 'IBM Plex Mono',ui-monospace,'SFMono-Regular',Consolas,monospace;
  font-family: var(--sans); color: ${C.ink}; background: ${C.paper};
  min-height: 100vh; padding: 16px; box-sizing: border-box; font-size: 13px;
}
.app *, .app *::before, .app *::after { box-sizing: border-box; }
.mono { font-family: var(--mono); font-variant-numeric: tabular-nums; }
.sub { color: ${C.sub}; font-weight: 400; font-size: 11px; }

.tblock {
  border: 1.5px solid ${C.ink}; background: ${C.panel}; border-radius: 10px;
  padding: 12px 16px; display: flex; justify-content: space-between; align-items: center; gap: 12px; flex-wrap: wrap;
  box-shadow: inset 0 0 0 3px ${C.paper}, inset 0 0 0 4px ${C.line};
}
.tb-title { font-size: 19px; font-weight: 700; letter-spacing: 0.06em; }
.tb-ver { font-size: 10px; color: ${C.sub}; letter-spacing: 0.12em; margin-left: 8px; }
.tb-sub { font-size: 12px; color: ${C.sub}; margin-top: 2px; }
.tb-vals { display: flex; gap: 8px; flex-wrap: wrap; }
.chip { border: 1px solid ${C.line}; border-radius: 8px; padding: 5px 10px; background: ${C.paper};
  display: flex; align-items: baseline; gap: 6px; font-size: 13px; }
.chip .ck { font-size: 10px; color: ${C.sub}; letter-spacing: 0.05em; }
.chip .cu { font-size: 10px; color: ${C.sub}; }

.grid { display: grid; grid-template-columns: 378px minmax(0,1fr); gap: 14px; margin-top: 14px; align-items: start; }
@media (max-width: 1080px) { .grid { grid-template-columns: 1fr; } }

.rail { display: flex; flex-direction: column; gap: 12px; }
.sheet { display: flex; flex-direction: column; gap: 12px; min-width: 0; }

.card { background: ${C.panel}; border: 1px solid ${C.line}; border-radius: 10px; padding: 12px 15px; }
.plotcard { padding: 10px 15px 6px; }
.card h3 { margin: 0 0 9px; font-size: 13.5px; font-weight: 700; letter-spacing: 0.01em; }
.cardhead { display: flex; justify-content: space-between; align-items: center; margin-bottom: 9px; gap: 8px; }
.cardhead h3 { margin: 0; }

.row { display: flex; gap: 10px; flex-wrap: wrap; align-items: center; margin-bottom: 7px; }
.num { display: inline-flex; align-items: center; gap: 5px; }
.num .nl { font-size: 12px; color: ${C.sub}; }
.num input, .nu { font-family: var(--mono); }
.num input {
  border: 1px solid ${C.line}; border-radius: 6px; padding: 4px 6px; font-size: 12.5px;
  background: #FBFCFA; color: ${C.ink};
}
.num input:focus, select:focus, button:focus-visible { outline: 2px solid ${C.shear}; outline-offset: 1px; }
.nu { font-size: 11px; color: ${C.sub}; }
.hint { font-size: 10.5px; color: ${C.sub}; margin: 2px 0 8px; }
.chk { display: inline-flex; align-items: center; gap: 6px; font-size: 12.5px; cursor: pointer; }
.chk input { accent-color: ${C.shear}; width: 14px; height: 14px; }

.loads { display: flex; flex-direction: column; gap: 6px; margin-top: 4px; }
.loadrow { display: flex; gap: 6px; align-items: center; flex-wrap: wrap; background: ${C.paper};
  border: 1px solid ${C.line}; border-radius: 7px; padding: 5px 7px; }
.loadrow select { font-family: var(--sans); font-size: 12px; border: 1px solid ${C.line}; border-radius: 6px;
  padding: 4px 4px; background: #fff; color: ${C.ink}; max-width: 168px; }
.xbtn { margin-left: auto; border: none; background: none; color: ${C.sub}; font-size: 15px; cursor: pointer;
  padding: 0 4px; border-radius: 5px; line-height: 1; }
.xbtn:hover { color: ${C.moment}; background: #F3E4E2; }
.addbtn { align-self: flex-start; border: 1px dashed ${C.grid}; background: none; color: ${C.sub};
  font-size: 11.5px; padding: 4px 9px; border-radius: 7px; cursor: pointer; font-family: var(--sans); }
.addbtn:hover { color: ${C.ink}; border-color: ${C.sub}; }
.minibtn, .resetbtn, .togbtn {
  border: 1px solid ${C.line}; background: ${C.paper}; color: ${C.sub}; font-size: 11px;
  padding: 3px 9px; border-radius: 7px; cursor: pointer; font-family: var(--sans); white-space: nowrap;
}
.minibtn:hover, .resetbtn:hover, .togbtn:hover { color: ${C.ink}; border-color: ${C.sub}; }
.togbtn { width: 100%; text-align: left; font-size: 12.5px; padding: 6px 10px; }

.suprow { display: flex; gap: 10px; align-items: flex-start; padding: 7px 0; border-top: 1px solid ${C.paper}; }
.suprow:first-of-type { border-top: none; }
.supname { font-size: 15px; padding-top: 3px; }
.supcols { display: flex; flex-direction: column; gap: 5px; flex: 1; }
.colline { display: flex; gap: 6px; align-items: center; flex-wrap: wrap; }
.cantblock { padding: 7px 0; border-top: 1px solid ${C.paper}; display: flex; flex-direction: column; gap: 6px; }
.cantblock:first-of-type { border-top: none; }

.plot { display: block; touch-action: none; }
.ptitle { font-size: 11.5px; font-weight: 700; letter-spacing: 0.04em; font-family: var(--sans); }
.preadout { font-size: 11px; font-family: var(--mono); }
.pzero { font-size: 9.5px; font-family: var(--mono); }
.plabel { font-size: 10.5px; font-weight: 600; font-family: var(--mono); }
.loadlbl { font-size: 10px; font-weight: 600; font-family: var(--mono); }
.jbadge { font-size: 13px; }
.rlabel { font-size: 9.5px; font-family: var(--mono); }
.dimlbl { font-size: 10px; font-family: var(--mono); }
.xaxis text { font-size: 9.5px; font-family: var(--mono); }

.tbl { width: 100%; border-collapse: collapse; font-size: 12px; }
.tbl th, .tbl td { border: 1px solid ${C.line}; padding: 4.5px 8px; text-align: right; }
.tbl th { background: ${C.paper}; font-weight: 600; font-size: 11px; color: ${C.sub}; }
.tbl td:first-child, .tbl th:first-child, .tbl td:nth-child(2):not(.mono) { text-align: center; }
.tbl tbody tr:hover { background: #F7F9F5; }
.tbl .sep { border-left: 2px solid ${C.grid}; }
.foot { font-size: 10.5px; color: ${C.sub}; margin: 7px 0 0; line-height: 1.5; }

.matwrap { margin-top: 9px; }
.dofchips { display: flex; flex-wrap: wrap; gap: 5px; margin-bottom: 8px; }
.dofchip { font-size: 10px; border: 1px solid ${C.line}; border-radius: 6px; padding: 2px 7px; background: ${C.paper}; color: ${C.sub}; }
.mattbl { overflow-x: auto; }
.mattbl .tbl { font-size: 10px; }
.mattbl .tbl th, .mattbl .tbl td { padding: 3px 6px; white-space: nowrap; }

.notes p { font-size: 11.5px; line-height: 1.65; margin: 0 0 7px; color: ${C.ink}; }
.errbox { color: ${C.moment}; font-weight: 600; }
.madeby { text-align: right; font-size: 10px; color: #98A29B; font-family: var(--mono); letter-spacing: 0.05em; margin-top: 10px; padding-right: 2px; }
.printbtn {
  border: 1px solid ${C.ink}; background: ${C.ink}; color: #fff; font-size: 12px; font-weight: 600;
  padding: 7px 14px; border-radius: 8px; cursor: pointer; font-family: var(--sans); letter-spacing: 0.02em;
}
.printbtn:hover { background: #33454F; }
.printbtn:disabled { opacity: 0.55; cursor: progress; }
.printonly { display: none; }
@media (prefers-reduced-motion: no-preference) {
  .card { transition: box-shadow .15s; }
}

/* ---------- A4 인쇄 ---------- */
@media print {
  @page { size: A4; margin: 12mm; }
  .app { background: #fff !important; padding: 0; font-size: 11.5px; min-height: auto; }
  .app * { -webkit-print-color-adjust: exact; print-color-adjust: exact; }
  .printonly { display: block; }
  .rail, .printbtn, .matcard { display: none !important; }
  .grid { display: block; margin-top: 8px; }
  .sheet { display: block; }
  .sheet > * { margin-bottom: 9px; }
  .tblock { box-shadow: none; break-inside: avoid; }
  .card { break-inside: auto; border-color: #AAB2AA; }
  .card:hover, .tbl tbody tr:hover { background: inherit; }
  .plot { width: 100% !important; height: auto !important; break-inside: avoid; }
  .plotcard { break-inside: auto; }
  .tbl { break-inside: auto; }
  .tbl tr { break-inside: avoid; }
  .card h3 { break-after: avoid; }
  .chip { background: #fff; }
  .notes p { font-size: 10.5px; }
}
`;
