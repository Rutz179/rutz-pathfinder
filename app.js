/* 러츠의 패스파인더 모험기 */
{
  const mul = seed => () => { seed = seed + 0x6D2B79F5 | 0; let t = Math.imul(seed ^ seed >>> 15, 1 | seed); t = t + Math.imul(t ^ t >>> 7, 61 | t) ^ t; return ((t ^ t >>> 14) >>> 0) / 4294967296; };
  const unseal = s => { const [k, d] = s.split("."), o = Uint8Array.from(atob(d), c => c.charCodeAt(0)), r = mul(parseInt(k, 36)), b = new Uint8Array(o.length); for (let i = 0; i < o.length; i++) b[i] = o[o.length - 1 - i] ^ (r() * 256 | 0); return JSON.parse(new TextDecoder().decode(b)); };
  const DRAFT = (() => { try { const g = JSON.parse(localStorage.getItem("gt-gm")); return g && g.draft ? JSON.parse(localStorage.getItem("gt-draft")) : null; } catch { return null; } })();
  const Q = DRAFT || (window.__gt ? unseal(window.__gt) : window.QUEST), S = Q.settings, R = S.recruit, AX = Object.keys(Q.axes);
  try { delete window.__gt; delete window.QUEST; } catch { window.__gt = window.QUEST = undefined; }
  const app = document.getElementById("app");
  const gmEl = document.getElementById("gm");
  const MARKS = { roman: ["I", "II", "III", "IV", "V", "VI", "VII"], alpha: ["a", "b", "c", "d", "e", "f", "g"], num: ["1", "2", "3", "4", "5", "6", "7"] }[S.markers] || ["I", "II", "III", "IV", "V", "VI", "VII"];
  const CAT = "art/cat.webp";
  const T0 = performance.now();

  /* ---------- 상태 ---------- */
  const store = {
    get: k => { try { return JSON.parse(localStorage.getItem("gt-" + k)); } catch { return null; } },
    set: (k, v) => { try { v == null ? localStorage.removeItem("gt-" + k) : localStorage.setItem("gt-" + k, JSON.stringify(v)); } catch { /* 저장소 없음 */ } }
  };
  let gm = store.get("gm");
  let torchPreview = false;
  let screen = "intro", run = null, result = null, busy = false, hidTimer = 0;
  const seats = { count: R.passed || 0, live: false };

  /* ---------- 유틸 ---------- */
  const esc = s => String(s ?? "").replace(/[&<>"']/g, c => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" }[c]));
  const shuffle = a => { a = a.slice(); for (let i = a.length - 1; i > 0; i--) { const j = Math.floor(Math.random() * (i + 1)); [a[i], a[j]] = [a[j], a[i]]; } return a; };
  const rng = seed => () => { seed = seed + 0x6D2B79F5 | 0; let t = Math.imul(seed ^ seed >>> 15, 1 | seed); t = t + Math.imul(t ^ t >>> 7, 61 | t) ^ t; return ((t ^ t >>> 14) >>> 0) / 4294967296; };
  const cyrb53 = (str, seed = 0) => { let h1 = 0xdeadbeef ^ seed, h2 = 0x41c6ce57 ^ seed; for (let i = 0, ch; i < str.length; i++) { ch = str.charCodeAt(i); h1 = Math.imul(h1 ^ ch, 2654435761); h2 = Math.imul(h2 ^ ch, 1597334677); } h1 = Math.imul(h1 ^ (h1 >>> 16), 2246822507); h1 ^= Math.imul(h2 ^ (h2 >>> 13), 3266489909); h2 = Math.imul(h2 ^ (h2 >>> 16), 2246822507); h2 ^= Math.imul(h1 ^ (h1 >>> 13), 3266489909); return (4294967296 * (2097151 & h2) + (h1 >>> 0)).toString(36); };
  const cat = cls => `<img class="cat ${cls}" src="${CAT}" alt="">`;
  const secOf = id => Q.sections.find(s => s.id === id) || { name: "" };
  const floorNo = id => Q.sections.findIndex(s => s.id === id) + 1;
  const showTorch = () => S.showTorch || torchPreview || !!(gm && gm.torch);
  const hiddenDelay = () => (gm && gm.fast ? 2 : S.hiddenDelay) * 1000;

  /* ---------- 출제: 층마다 core는 항상, 나머지는 pick 수만큼 무작위 ---------- */
  function newRun() {
    const order = [];
    for (const s of Q.sections) {
      const idx = Q.questions.map((q, i) => q.section === s.id && !q.off ? i : -1).filter(i => i >= 0);
      let chosen = idx;
      if (s.pick != null && !(gm && gm.all)) {
        const core = idx.filter(i => Q.questions[i].core);
        const rest = shuffle(idx.filter(i => !Q.questions[i].core));
        chosen = core.concat(rest.slice(0, Math.max(0, s.pick - core.length))).sort((a, b) => a - b);
      }
      order.push(...chosen);
    }
    const optOrder = {};
    for (const qi of order) {
      const q = Q.questions[qi], vis = [], hid = [];
      q.options.forEach((o, i) => (o.hidden ? hid : vis).push(i));
      optOrder[qi] = (S.shuffleAll !== false || q.shuffle ? shuffle(vis) : vis).concat(hid);
    }
    return { order, optOrder, ans: [], times: [], pos: 0, revealed: {}, ghost: null, shownPos: -1, shownAt: 0 };
  }
  const pairsOf = r => r.ans.map((oi, p) => [r.order[p], oi]);

  /* ---------- 채점 ---------- */
  const SP = Object.assign({ msPerChar: 12, min: 1.5, max: 4, burn: 2 }, S.speed);
  const minRead = q => Math.min(SP.max * 1000, Math.max(SP.min * 1000, (q.text.length + q.options.filter(o => !o.hidden).reduce((a, o) => a + o.t.length, 0)) * SP.msPerChar));
  function evaluate(pairs, times, always) {
    let torch = S.torchStart, fit = 0, fmin = 0, fmax = 0, died = null, hidden = 0, fast = 0;
    const speedOn = times && (always || !(gm && gm.nospeed)) && SP.burn > 0;
    const ax = {}, amax = {};
    AX.forEach(k => { ax[k] = 0; amax[k] = 0; });
    pairs.forEach(([qi, oi], step) => {
      const q = Q.questions[qi], o = q.options[oi], w = q.weight ?? 1;
      const fits = q.options.filter(x => !x.hidden).map(x => x.fit || 0);
      fit += (o.fit || 0) * w; fmin += Math.min(...fits) * w; fmax += Math.max(...fits) * w;
      AX.forEach(k => {
        ax[k] += (o.fx && o.fx[k]) || 0;
        amax[k] += Math.max(0, ...q.options.filter(x => !x.hidden).map(x => (x.fx && x.fx[k]) || 0));
      });
      if (o.hidden) hidden++;
      torch -= o.burn || 0;
      if (torch <= 0 && !died) died = { step, key: o.death || "default" };
      if (speedOn && times[step] != null && times[step] < minRead(q)) {
        fast++; torch -= SP.burn;
        if (torch <= 0 && !died) died = { step, key: "speedrun" };
      }
    });
    const pct = fmax > fmin ? Math.max(0, Math.min(100, Math.round((fit - fmin) / (fmax - fmin) * 100))) : 100;
    const axp = {};
    let type = "none", best = 0;
    AX.forEach(k => {
      axp[k] = amax[k] > 0 ? Math.max(0, Math.min(1, ax[k] / amax[k])) : null;
      if (axp[k] != null && ax[k] > 0 && axp[k] > best + 1e-9) { best = axp[k]; type = k; }
    });
    return { torch, fit: pct, axp, type, died, hidden, fast, n: pairs.length };
  }

  /* ---------- 결과 코드 (GM 패널에서 해독) ---------- */
  const chk = s => { let h = 7; for (const c of s) h = (h * 31 + c.charCodeAt(0)) % 1296; return h.toString(36).padStart(2, "0"); };
  // 방마다 걸린 시간은 0.5초 단위(최대 17.5초)로 한 글자씩 기록
  const makeCode = (pairs, fit, times, total) => {
    const body = pairs.map(([qi, oi], p) => qi.toString(36).padStart(2, "0") + oi.toString(36) + Math.min(35, Math.floor((times[p] || 0) / 500)).toString(36)).join("");
    const head = `${fit}-${Math.round(total / 1000).toString(36)}`;
    return `${S.discord.codePrefix || ""}${head}-${body}-${chk(head + body)}`;
  };
  function readCode(code) {
    const m = String(code).trim().toLowerCase().match(/^[a-z]*(\d+)-([0-9a-z]+)-([0-9a-z]+)-([0-9a-z]{2})$/);
    if (!m) return { err: "코드 형식이 아닙니다." };
    if (chk(`${m[1]}-${m[2]}` + m[3]) !== m[4] || m[3].length % 4) return { err: "코드 일부가 잘렸거나 바뀐 것 같습니다." };
    const pairs = [], times = [];
    for (let i = 0; i < m[3].length; i += 4) {
      const qi = parseInt(m[3].slice(i, i + 2), 36), oi = parseInt(m[3][i + 2], 36);
      if (!Q.questions[qi] || !Q.questions[qi].options[oi]) return { err: "지금 문항 목록과 맞지 않는 코드입니다." };
      pairs.push([qi, oi]); times.push(parseInt(m[3][i + 3], 36) * 500 + 250);
    }
    return { pairs, times, total: parseInt(m[2], 36) };
  }

  /* ---------- 자리 카운터 (Cloudflare Worker) ---------- */
  async function counter(method) {
    if (!R.counterUrl) return null;
    try {
      const ctl = new AbortController(); setTimeout(() => ctl.abort(), 4000);
      const res = await fetch(R.counterUrl, { method, signal: ctl.signal });
      return res.ok ? await res.json() : null;
    } catch { return null; }
  }
  const isFull = () => seats.count >= R.cap;
  const dur = ms => { const s = Math.round(ms / 1000); return s >= 60 ? `${Math.floor(s / 60)}분 ${s % 60}초` : `${s}초`; };

  /* ---------- 손그림 지도 ---------- */
  function mapSVG(cur, deadAt = -1, ghost = null) {
    const order = run.order, n = order.length, W = 560, cols = Math.min(n, 10), rows = Math.ceil(n / cols);
    const s = 22, pad = 8, stepX = cols > 1 ? (W - pad * 2 - s) / (cols - 1) : 0, stepY = 48;
    const H = (rows - 1) * stepY + s + 22;
    const r = rng(7), j = v => (r() - .5) * v;
    const pts = [];
    for (let i = 0; i < n; i++) {
      const row = Math.floor(i / cols), c = i % cols, col = row % 2 ? cols - 1 - c : c;
      pts.push([pad + col * stepX + j(8), 10 + row * stepY + j(9)]);
    }
    const side = (x1, y1, x2, y2) => {
      const dx = x2 - x1, dy = y2 - y1, L = Math.hypot(dx, dy) || 1, ox = dx / L * 2, oy = dy / L * 2;
      return `M${(x1 - ox).toFixed(1)} ${(y1 - oy).toFixed(1)}L${(x2 + ox).toFixed(1)} ${(y2 + oy).toFixed(1)}`;
    };
    let cors = "", rooms = "";
    for (let i = 1; i < n; i++) {
      const a = pts[i - 1], b = pts[i], ax = a[0] + s / 2, ay = a[1] + s / 2, bx = b[0] + s / 2, by = b[1] + s / 2;
      const mx = (ax + bx) / 2 + j(6), my = (ay + by) / 2 + j(6);
      cors += `<path class="cor${i <= cur ? " done" : ""}" d="M${ax.toFixed(1)} ${ay.toFixed(1)}Q${mx.toFixed(1)} ${my.toFixed(1)} ${bx.toFixed(1)} ${by.toFixed(1)}"/>`;
      if (Q.questions[order[i]].section !== Q.questions[order[i - 1]].section) {
        const L = Math.hypot(bx - ax, by - ay) || 1, nx = -(by - ay) / L * 5, ny = (bx - ax) / L * 5, ux = (bx - ax) / L * 4, uy = (by - ay) / L * 4, cx = (ax + bx) / 2, cy = (ay + by) / 2;
        cors += [-1, 0, 1].map(k => `<path class="stairs" d="M${(cx + ux * k - nx).toFixed(1)} ${(cy + uy * k - ny).toFixed(1)}L${(cx + ux * k + nx).toFixed(1)} ${(cy + uy * k + ny).toFixed(1)}"/>`).join("");
      }
    }
    pts.forEach(([x, y], i) => {
      const c = [[x + j(2), y + j(2)], [x + s + j(2), y + j(2)], [x + s + j(2), y + s + j(2)], [x + j(2), y + s + j(2)]];
      let cls = i < cur ? "done" : i === cur ? "cur" : "todo";
      if (ghost != null && i > ghost && i < cur) cls += " ghost";
      rooms += `<g class="room ${cls}"><path class="fill" d="M${c.map(p => p.map(v => v.toFixed(1)).join(" ")).join("L")}Z"/><path class="edge" d="${c.map((p, k) => side(...p, ...c[(k + 1) % 4])).join("")}"/></g>`;
      if (i === cur && deadAt < 0) {
        const fx = x + s / 2, fy = y + s / 2 + 2;
        rooms += `<path class="flame${ghost != null ? " ghost" : ""}" d="M${fx} ${fy - 10}C${fx + 6} ${fy - 3} ${fx + 5} ${fy + 4} ${fx} ${fy + 5}C${fx - 5} ${fy + 4} ${fx - 6} ${fy - 2} ${fx} ${fy - 10}Z"/>`;
      }
      if (i === deadAt || (ghost != null && i === ghost)) rooms += `<path class="dead" d="M${x + 4} ${y + 4}L${x + s - 4} ${y + s - 4}M${x + s - 4} ${y + 4}L${x + 4} ${y + s - 4}"/>`;
    });
    return `<svg class="map" viewBox="-4 -6 ${W + 8} ${H}" role="img" aria-label="던전 지도, 방 ${n}개">${cors}<g class="rooms">${rooms}</g></svg>`;
  }

  /* ---------- 화면: 시작 ---------- */
  function viewIntro() {
    const n = run.order.length, mins = Math.max(3, Math.round(n * 13 / 60));
    const seatLine = R.closed ? "이번 모집은 마감되었어요. 시험은 재미로 해 볼 수 있습니다."
      : isFull() ? `정원 ${R.cap}명이 찼어요. 지금 통과하면 예비 모험가 명부에 올라갑니다.`
      : `지금까지 최심부에 도달한 모험가 <span class="nw">${seats.count} / ${R.cap}명</span>`;
    return `<article class="sheet enter">
      ${mapSVG(0)}
      <div class="hero">
        <div><p class="sub">${esc(Q.meta.sub)}</p><h1 class="title">${esc(Q.meta.title)}</h1></div>
        ${cat("hero-cat")}
      </div>
      <p class="lead">${esc(Q.meta.lead)}</p>
      <ul class="notice">${Q.meta.notice.map(t => `<li>${esc(t)}</li>`).join("")}</ul>
      <p class="seats">${seatLine}</p>
      <hr class="rule">
      <p class="honest">방은 ${n}개, ${mins}분 정도 걸립니다. ${esc(Q.meta.honesty)}</p>
      <button class="btn" data-act="start">${esc(Q.meta.start)}</button>
      <p class="colophon">${esc(Q.meta.credit)}</p>
    </article>`;
  }

  /* ---------- 화면: 방 ---------- */
  function scoreNote(q, o) {
    if (!(gm && gm.scores)) return "";
    const w = q.weight ?? 1, fx = Object.entries(o.fx || {}).map(([k, v]) => `${Q.axes[k]}${v > 0 ? "+" : ""}${v}`).join(" ");
    return `<span class="gm-note">궁합 ${o.fit || 0}×${w}${o.burn ? `, 횃불 -${o.burn}` : ""}${fx ? `, ${fx}` : ""}${o.death ? `, ${o.death}` : ""}</span>`;
  }

  function viewRoom(animate) {
    const { pos, order } = run, qi = order[pos], q = Q.questions[qi], n = order.length;
    const ev = evaluate(pairsOf(run).slice(0, pos), run.times);
    const revealed = !!run.revealed[pos];
    let k = 0;
    const opts = run.optOrder[qi].map(oi => {
      const o = q.options[oi];
      if (o.hidden && !revealed) { k++; return ""; }
      return `<li class="${o.hidden ? "secret" : ""}"><button class="opt${run.ans[pos] === oi ? " on" : ""}" data-oi="${oi}"><span class="mk" aria-hidden="true">${MARKS[k++] || k}</span><span>${esc(o.t)}${scoreNote(q, o)}</span></button></li>`;
    }).join("");
    const hasHidden = q.options.some(o => o.hidden);
    const torch = showTorch()
      ? `<span class="torch" role="img" aria-label="남은 횃불 ${Math.max(0, ev.torch)}">${Array.from({ length: S.torchStart }, (_, i) => `<i class="${i < ev.torch ? "lit" : ""}"></i>`).join("")}</span>` : "";
    return `<article class="sheet${animate ? " enter" : ""}">
      ${mapSVG(pos, -1, run.ghost)}
      <p class="floor">${esc(secOf(q.section).name)}</p>
      <h2 class="room-no" tabindex="-1">방 ${pos + 1}<small>/ ${n}</small></h2>
      ${run.ghost != null ? `<p class="ghost-note">유령이 되어 둘러보는 중입니다. 결과는 볼 수 있지만, 문은 열리지 않아요.</p>` : ""}
      <p class="q">${esc(q.text)}</p>
      ${q.tags ? `<ul class="tags">${q.tags.map(t => `<li>${esc(t)}</li>`).join("")}</ul>` : ""}
      <ol class="opts">${opts}</ol>
      ${hasHidden ? `<p class="hint"${revealed ? "" : " hidden"}>${cat("hint-cat")}<span>오래 고민하는 당신 곁에서, 고양이가 벽 틈을 찾아냈습니다.</span></p>` : ""}
      <div class="foot"><button class="link" data-act="back"${pos === 0 || (run.ghost != null && pos === run.ghost + 1) ? " disabled" : ""}>이전 방으로</button>${torch}</div>
    </article>`;
  }

  function reveal() {
    run.revealed[run.pos] = true;
    render(false);
    app.querySelectorAll(".opts li.secret, .hint").forEach(el => el.classList.add("reveal"));
  }

  /* ---------- 화면: 결과 ---------- */
  function typeBlock(ev, label, seal) {
    const t = Q.types[ev.type] || Q.types.none;
    const bars = AX.filter(k => ev.axp[k] != null).map(k =>
      `<span>${esc(Q.axes[k])}</span><span class="bar"><i style="width:${Math.round(ev.axp[k] * 100)}%"></i></span>`).join("");
    return `<section class="card">
        ${seal ? `<div class="seal" aria-hidden="true"><span>R</span></div>` : ""}
        <p class="where">${esc(label)}</p>
        <h2 class="typename">${esc(t.name)}</h2>
        <p>${esc(t.desc)}</p>
        <div class="bars">${bars}</div>
        ${ev.hidden ? `<p class="found">숨은 길을 ${ev.hidden}개 찾아냈습니다. 고민이 깊은 모험가시군요.</p>` : ""}
      </section>`;
  }

  function gateBlock() {
    let url = "";
    try { url = S.discord.url || (S.discord.urlB64 ? atob(S.discord.urlB64) : ""); } catch { url = ""; }
    const link = label => url
      ? `<a class="btn" href="${esc(url)}" target="_blank" rel="noopener">${label}</a>`
      : `<p class="note">디스코드 링크가 아직 비어 있습니다.</p>`;
    const code = `<details class="code"><summary>GM에게 보여 줄 답안지 코드</summary>
        <div class="codebox"><input id="code" readonly value="${esc(result.code)}" aria-label="결과 코드"><button class="btn sm" data-act="copy">복사</button></div></details>`;
    if (R.closed) return `<section class="gate"><p>이번 모집은 마감되었어요. 그래도 끝까지 와 줘서 고마워요!</p></section>`;
    if (result.seat === "wait") return `<section class="gate"><p class="note">자리를 확인하는 중…</p></section>`;
    const reserve = result.seat != null ? result.seat > R.cap : isFull();
    if (reserve) return `<section class="gate"><p class="score">예비 모험가</p>
        <p>정원 ${R.cap}명이 이미 찼어요. 예비 모험가 명부에 이름을 올려 주세요. 자리가 나거나 다음 모집 때 먼저 연락드릴게요.</p>
        ${R.reserveLink ? `<div class="row">${link("예비 모험가로 들어가기")}</div>` : ""}${code}</section>`;
    const nth = result.seat != null ? `${result.seat}번째로 최심부에 도달한 모험가입니다. (정원 ${R.cap}명)` : `궁합 ${result.ev.fit}%`;
    return `<section class="gate"><p class="score">${esc(nth)}</p>
        <p>들어오면 GM과 짧게 보이스로 인사를 나눠요. 그다음엔 2~3주 시험 세션!</p>
        <div class="row">${cat("gate-cat")}${link("디스코드로 가기")}</div>${code}</section>`;
  }

  function viewEnd() {
    const { kind, ev } = result, E = Q.endings;
    const retry = S.allowRetry ? `<button class="link" data-act="retry">처음부터 다시</button>` : "";
    if (kind === "dark") {
      const d = ev.died, D = E.deaths[d.key] || E.deaths.default, q = Q.questions[run.order[d.step]];
      const t = Q.types[ev.type] || Q.types.none;
      return `<article class="sheet enter">
        ${mapSVG(d.step, d.step)}
        <p class="where">지하 ${floorNo(q.section)}층, 방 ${d.step + 1}에서</p>
        <h1 class="title">${esc(E.dark.title)}</h1>
        <div class="grave-row">
          ${cat("grave-cat")}
          <section class="grave">
            <p class="rip">여기 「${esc(t.name)}」 잠들다</p>
            <p class="cause">사인: ${esc(D.cause)}</p>
            <p class="epitaph">${esc(D.text)}</p>
          </section>
        </div>
        ${ev.n >= 6 ? typeBlock(ev, "지금까지 보인 당신의 모습") : `<p class="early">당신을 알아보기엔 너무 이른 죽음이었어요. 유령이 되어 끝까지 둘러보면, 어떤 모험가였는지 알려 드릴게요.</p>`}
        <p class="honest">던전에 머문 시간 ${dur(result.total)}. ${esc(E.dark.after)}</p>
        <div class="row"><button class="btn" data-act="ghost">유령이 되어 끝까지 둘러보기</button>${retry}</div>
      </article>`;
    }
    const e = E[kind];
    const ghostLine = kind === "ghost" ? (() => { const d = evaluate(pairsOf(run).slice(0, run.ghost + 1)).died, D = E.deaths[d?.key] || E.deaths.default; return `<p class="where">사인: ${esc(D.cause)} (방 ${run.ghost + 1})</p>`; })() : "";
    return `<article class="sheet enter">
      ${mapSVG(run.order.length, -1, kind === "ghost" ? run.ghost : null)}
      ${ghostLine}
      <h1 class="title">${esc(e.title)}</h1>
      <p class="lead">${esc(e.text)}</p>
      <p class="note">던전에 머문 시간 ${dur(result.total)}</p>
      ${typeBlock(ev, kind === "ghost" ? "끝까지 둘러본 당신의 모습" : "당신의 모험가 유형", kind === "clear")}
      ${kind === "clear" ? gateBlock() : kind === "home" ? `<div class="row">${cat("gate-cat small")}</div>` : ""}
      <div class="row">${retry}</div>
    </article>`;
  }

  /* ---------- 화면: 결과 코드 해독 (GM 전용) ---------- */
  function viewDecode() {
    return `<article class="sheet enter decode">
      <h1 class="title">결과 코드 해독</h1>
      <p class="lead">지원자가 보낸 코드를 붙여 넣으면 어떤 답을 골랐는지 보여 줍니다.</p>
      <textarea id="codein" rows="3" aria-label="결과 코드"></textarea>
      <div class="row"><button class="btn sm" data-act="decodeGo">해독하기</button><button class="link" data-act="home">처음 화면으로</button></div>
      <div id="decoded"></div>
    </article>`;
  }
  function decodedHTML(code) {
    const r = readCode(code);
    if (r.err) return `<p class="err">${esc(r.err)}</p>`;
    const ev = evaluate(r.pairs, r.times, true), t = Q.types[ev.type] || Q.types.none;
    const head = (ev.died ? `방 ${ev.died.step + 1}에서 횃불이 꺼짐 (${ev.died.key})` : `궁합 ${ev.fit}%, 남은 횃불 ${ev.torch}, 숨은 길 ${ev.hidden}개`) + `, 총 ${dur(r.total * 1000)}, 빠른 답 ${ev.fast}개`;
    const rows = r.pairs.map(([qi, oi], p) => {
      const q = Q.questions[qi], o = q.options[oi], w = q.weight ?? 1;
      const sec = r.times[p] >= 17500 ? "17초 이상" : `약 ${(r.times[p] / 1000).toFixed(1)}초`, quick = r.times[p] < minRead(q);
      return `<li><span class="m">방 ${p + 1}</span> ${esc(q.text.length > 46 ? q.text.slice(0, 46) + "…" : q.text)}<br><b>${esc(o.t)}</b> <span class="m">궁합 ${(o.fit || 0) * w}${o.burn ? `, 횃불 -${o.burn}` : ""}${o.hidden ? ", 숨은 길" : ""}, ${sec}${quick ? " (빠른 답)" : ""}</span></li>`;
    }).join("");
    return `<p class="score">${esc(head)}</p><p>${esc(t.name)}</p><ul class="dlist">${rows}</ul>`;
  }

  /* ---------- 그리기 ---------- */
  function render(animate = true) {
    clearTimeout(hidTimer);
    if (screen === "room" && run.shownPos !== run.pos) { run.shownPos = run.pos; run.shownAt = performance.now(); }
    app.innerHTML = screen === "room" ? viewRoom(animate) : screen === "end" ? viewEnd() : screen === "decode" ? viewDecode() : viewIntro();
    app.querySelectorAll("img").forEach(img => { const drop = () => img.remove(); img.addEventListener("error", drop); if (img.complete && img.naturalWidth === 0) drop(); });
    if (screen === "room" && !run.revealed[run.pos] && Q.questions[run.order[run.pos]].options.some(o => o.hidden)) hidTimer = setTimeout(reveal, hiddenDelay());
    renderGM();
  }
  function toTop() {
    const el = app.querySelector(".room-no") || app.querySelector("h1");
    el?.focus?.({ preventScroll: true });
    if (window.scrollY > 0) window.scrollTo(0, 0);
  }

  /* ---------- 진행 ---------- */
  function choose(oi, btn) {
    if (busy) return;
    busy = true;
    clearTimeout(hidTimer);
    btn.closest(".opts").classList.add("locked");
    btn.classList.add("on");
    const took = performance.now() - run.shownAt;
    setTimeout(() => {
      busy = false;
      run.ans[run.pos] = oi; run.times[run.pos] = Math.max(took, run.times[run.pos] || 0); // 다시 고른 방은 처음 읽은 시간을 인정
      run.ans.length = run.times.length = run.pos + 1;
      run.shownPos = -1;
      const pairs = pairsOf(run), ev = evaluate(pairs, run.times);
      if (ev.died && run.ghost == null) return finish("dark", ev, pairs);
      if (run.pos + 1 >= run.order.length) return finish(run.ghost != null ? "ghost" : ev.fit >= S.passScore ? "clear" : "home", ev, pairs);
      run.pos++;
      render(); toTop();
    }, 260);
  }

  async function finish(kind, ev, pairs) {
    const total = performance.now() - T0;
    result = { kind, ev, total, code: makeCode(pairs, ev.fit, run.times, total), seat: null };
    screen = "end";
    const count = kind === "clear" && !gm && !R.closed && R.counterUrl;
    if (count) result.seat = "wait";
    render(); toTop();
    if (count) {
      const res = await counter("POST");
      if (res && res.seat) { result.seat = res.seat; seats.count = res.count; seats.live = true; } else result.seat = null;
      if (screen === "end") render(false);
    }
  }

  app.addEventListener("click", e => {
    const opt = e.target.closest(".opt");
    if (opt) return choose(+opt.dataset.oi, opt);
    const b = e.target.closest("[data-act]");
    if (!b) return;
    const act = b.dataset.act;
    if (act === "start") { screen = "room"; run.pos = 0; render(); toTop(); }
    else if (act === "back" && run.pos > 0) { run.pos--; run.shownPos = -1; render(); }
    else if (act === "retry") { run = newRun(); result = null; screen = "room"; render(); toTop(); }
    else if (act === "ghost") { run.ghost = result.ev.died.step; run.pos = run.ghost + 1; screen = run.pos < run.order.length ? "room" : "end"; if (screen === "end") result.kind = "ghost"; render(); toTop(); }
    else if (act === "home") { screen = "intro"; render(); }
    else if (act === "decodeGo") { document.getElementById("decoded").innerHTML = decodedHTML(document.getElementById("codein").value); }
    else if (act === "copy") copy(document.getElementById("code").value, b, "복사됨");
  });

  function copy(text, btn, done) {
    const fallback = () => { btn.textContent = "직접 선택해서 복사해 주세요"; };
    try { navigator.clipboard.writeText(text).then(() => { btn.textContent = done; }, fallback); } catch { fallback(); }
  }

  document.addEventListener("keydown", e => {
    if (screen !== "room" || busy || e.metaKey || e.ctrlKey || e.altKey || /input|textarea/i.test(e.target.tagName)) return;
    const k = parseInt(e.key, 10);
    if (k >= 1) { const btns = [...app.querySelectorAll(".opts .opt")]; if (btns[k - 1]) choose(+btns[k - 1].dataset.oi, btns[k - 1]); }
  });

  /* ---------- 관리 ---------- */
  function renderGM() {
    gmEl.hidden = !gm;
    if (!gm) return;
    const ev = screen === "end" && result ? result.ev : run ? evaluate(pairsOf(run), run.times) : null;
    const box = (k, label) => `<label><input type="checkbox" data-gm="${k}"${gm[k] ? " checked" : ""}> ${label}</label>`;
    const open = gmEl.querySelector("details")?.open ?? true;
    gmEl.innerHTML = `<details${open ? " open" : ""}><summary>GM 패널${DRAFT ? " (편집기 초안 사용 중)" : ""}</summary>
      ${box("draft", "편집기 초안으로 플레이 (새로고침)")}${box("scores", "점수 보기")}${box("torch", "횃불 보이기")}${box("nospeed", "속도 판정 끄기")}${box("fast", "숨은 길 2초")}${box("all", "문항 전부 출제 (다음 판부터)")}
      ${ev ? `<p>횃불 ${ev.torch}/${S.torchStart}, 궁합 ${ev.fit}% (통과 ${S.passScore}), 빠른 답 ${ev.fast}, ${esc(Q.types[ev.type]?.name || "-")}</p>` : ""}
      ${screen === "room" ? `<p class="dim">이 방 최소 읽기 시간 ${(minRead(Q.questions[run.order[run.pos]]) / 1000).toFixed(1)}초</p>` : ""}
      <p class="dim">GM 모드에서는 통과해도 자리 수가 올라가지 않아요.</p>
      <div class="gm-btns"><button data-gmact="decode">결과 코드 해독</button><button data-gmact="torchlink">횃불 체험 링크 복사</button><button data-gmact="off">GM 모드 끄기</button></div>
      <p class="dim">문항, 암호, 디코 링크는 tools/editor.html에서 고칩니다.</p>
    </details>`;
  }
  gmEl.addEventListener("change", e => {
    const k = e.target.dataset.gm; if (!k) return;
    gm[k] = e.target.checked; store.set("gm", gm);
    if (k === "draft") return location.reload();
    render(false);
  });
  gmEl.addEventListener("click", e => {
    const act = e.target.dataset.gmact; if (!act) return;
    if (act === "decode") { screen = "decode"; render(); }
    else if (act === "torchlink") copy(location.href.split("#")[0] + "#torch", e.target, "복사됨");
    else if (act === "off") { gm = null; store.set("gm", null); render(false); }
  });

  function onHash() {
    const h = location.hash.slice(1);
    if (!h) return;
    if (h === "torch") { torchPreview = true; render(false); return; }
    if (h.startsWith("gm-") && cyrb53(h.slice(3)) === S.gm.hash) {
      gm = gm || { scores: true, torch: false, fast: false, all: false };
      store.set("gm", gm);
      try { history.replaceState(null, "", location.pathname + location.search); } catch { /* 무시 */ }
      render(false);
    }
  }
  window.addEventListener("hashchange", onHash);

  run = newRun();
  render();
  onHash();
  counter("GET").then(res => { if (res && typeof res.count === "number") { seats.count = res.count; seats.live = true; if (screen === "intro") render(false); } });
}
