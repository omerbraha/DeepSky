import { describe, it, expect } from 'vitest';
const fs = require('fs');
const path = require('path');

/**
 * Regression tests for two related v1.2.x improvements:
 *
 *   1. Copy-last-prompt button in the SESSION CONTEXT bar
 *      (`#terminal-prompt-ghost`).
 *   2. Status indicator overhaul:
 *        - "Working → Waiting" transition is now driven by a per-session
 *          debounce timer that fires ~1.2 s after the last pty:data chunk,
 *          instead of the previous ~39 s polling decay.
 *        - "Pending PR" fires only when the latest assistant.message in
 *          events.jsonl contains a PR URL, via `session.lastAssistantHasPR`,
 *          instead of any historical PR resource in the session.
 *
 * Like the rest of the renderer wiring tests, this asserts against source
 * text — spinning up xterm + Electron in jsdom is impractical.
 */

const rendererPath = path.join(__dirname, '..', 'src', 'renderer.js');
const preloadPath = path.join(__dirname, '..', 'src', 'preload.js');
const mainPath = path.join(__dirname, '..', 'src', 'main.js');
const cssPath = path.join(__dirname, '..', 'src', 'styles.css');
const indexHtmlPath = path.join(__dirname, '..', 'src', 'index.html');

const renderer = fs.readFileSync(rendererPath, 'utf8');
const preload = fs.readFileSync(preloadPath, 'utf8');
const main = fs.readFileSync(mainPath, 'utf8');
const css = fs.readFileSync(cssPath, 'utf8');
const indexHtml = fs.readFileSync(indexHtmlPath, 'utf8');

describe('copy-last-prompt button in the SESSION CONTEXT bar', () => {
  it('IPC accepts a { full } option for getLastUserPrompt end-to-end', () => {
    // preload forwards the options argument
    expect(preload).toMatch(
      /getLastUserPrompt:\s*\(sessionId,\s*options\)\s*=>\s*ipcRenderer\.invoke\(['"]session:getLastUserPrompt['"],\s*sessionId,\s*options\)/
    );
    // main accepts and forwards the options argument
    expect(main).toMatch(
      /ipcMain\.handle\(\s*['"]session:getLastUserPrompt['"][\s\S]*?async\s*\(event,\s*sessionId,\s*options\)[\s\S]*?sessionService\.getLastUserPrompt\(sessionId,\s*options\)/
    );
  });

  it('updateSessionPromptGhost renders a .prompt-copy-btn with a data-session-id', () => {
    const m = renderer.match(/function updateSessionPromptGhost[\s\S]*?\n\}/);
    expect(m, 'updateSessionPromptGhost body must be findable').not.toBeNull();
    const body = m[0];
    // The button is rendered into the prompt-ghost innerHTML
    expect(body).toMatch(/prompt-copy-btn/);
    // The session id is captured at render time (rubber-duck: avoid copying
    // the wrong session if activeSessionId changes between render and click)
    expect(body).toMatch(/data-session-id=["']?\$\{(?:esc\()?sessionId/);
    // Button is only shown when there's actually a lastPrompt to copy
    const promptBranchIdx = body.indexOf('if (lastPrompt)');
    const copyBtnIdx = body.indexOf('prompt-copy-btn');
    expect(promptBranchIdx).toBeGreaterThan(-1);
    expect(copyBtnIdx).toBeGreaterThan(promptBranchIdx);
  });

  it('wires the copy click via event delegation on the stable prompt-ghost parent', () => {
    // Event delegation is required because innerHTML is rewritten on every
    // ghost update, so a direct listener would be wiped.
    expect(renderer).toMatch(
      /terminalPromptGhost\.addEventListener\(['"]click['"][\s\S]*?\.closest\(['"]\.prompt-copy-btn['"]\)/
    );
  });

  it('copy handler reads sessionId from the button (not activeSessionId) and calls copyText with the full prompt', () => {
    const m = renderer.match(/terminalPromptGhost\.addEventListener\(['"]click['"][\s\S]*?\n\s*\}\);/);
    expect(m, 'click delegation handler must be findable').not.toBeNull();
    const body = m[0];
    expect(body).toMatch(/btn\.dataset\.sessionId/);
    expect(body).toMatch(/getLastUserPrompt\(sessionId,\s*\{\s*full:\s*true\s*\}\)/);
    expect(body).toMatch(/copyText\(/);
    // The handler should not blindly read activeSessionId — that's the
    // exact race we're guarding against.
    expect(body).not.toMatch(/activeSessionId\b/);
  });

  it('prompt-ghost is no longer aria-hidden (now contains an interactive button)', () => {
    // Earlier the bar was aria-hidden="true" because it was purely
    // decorative; adding an interactive button means it must be exposed.
    expect(indexHtml).toMatch(/id="terminal-prompt-ghost" class="terminal-prompt-ghost"\s*>/);
    expect(indexHtml).not.toMatch(/id="terminal-prompt-ghost"[^>]*aria-hidden=/);
  });

  it('CSS defines a .prompt-copy-btn inside the prompt-ghost with hover/focus/copied states', () => {
    expect(css).toMatch(/\.terminal-prompt-ghost\s+\.prompt-copy-btn\s*\{/);
    expect(css).toMatch(/\.terminal-prompt-ghost\s+\.prompt-copy-btn:hover/);
    expect(css).toMatch(/\.terminal-prompt-ghost\s+\.prompt-copy-btn:focus-visible/);
    expect(css).toMatch(/\.terminal-prompt-ghost\s+\.prompt-copy-btn\.copied/);
  });
});

describe('per-session debounce timer makes Working → Waiting near-instant', () => {
  it('declares a sessionBusyTimers Map and tuned constants', () => {
    expect(renderer).toMatch(/const sessionBusyTimers\s*=\s*new Map\(\)/);
    // The old "wait 30 s before even considering idle" threshold is gone
    expect(renderer).not.toMatch(/BUSY_THRESHOLD_MS\s*=\s*30000/);
    expect(renderer).toMatch(/BUSY_THRESHOLD_MS\s*=\s*1500/);
    // Debounce is at least 1500ms — long enough to absorb brief spinner
    // pauses without flicker.
    const m = renderer.match(/BUSY_DEBOUNCE_MS\s*=\s*(\d+)/);
    expect(m, 'BUSY_DEBOUNCE_MS must be declared').not.toBeNull();
    expect(Number(m[1])).toBeGreaterThanOrEqual(1500);
  });

  it('markSessionBusy sets busy=true, resets any pending timer, and schedules a flip to Waiting', () => {
    const m = renderer.match(/function markSessionBusy[\s\S]*?\n\}/);
    expect(m, 'markSessionBusy body must be findable').not.toBeNull();
    const body = m[0];
    expect(body).toMatch(/sessionBusyState\.set\(sessionId,\s*true\)/);
    expect(body).toMatch(/clearTimeout\(existing\)/);
    expect(body).toMatch(/setTimeout\([\s\S]*?BUSY_DEBOUNCE_MS\)/);
    // When the debounce fires, busy must flip to false and the badge must
    // be repainted so the user sees Working → Waiting immediately.
    expect(body).toMatch(/sessionBusyState\.set\(sessionId,\s*false\)/);
    expect(body).toMatch(/schedulePatchSessionStateBadges\(sessionId\)/);
  });

  it('clearSessionBusy clears the debounce timer + busy flag + idle counter together', () => {
    const m = renderer.match(/function clearSessionBusy[\s\S]*?\n\}/);
    expect(m, 'clearSessionBusy body must be findable').not.toBeNull();
    const body = m[0];
    expect(body).toMatch(/sessionBusyTimers\.get\(sessionId\)/);
    expect(body).toMatch(/clearTimeout\(timer\)/);
    expect(body).toMatch(/sessionBusyTimers\.delete\(sessionId\)/);
    expect(body).toMatch(/sessionBusyState\.delete\(sessionId\)/);
    expect(body).toMatch(/sessionIdleCount\.delete\(sessionId\)/);
  });

  it('pty:data listener invokes markSessionBusy (not the bare sessionBusyState.set) and only on substantive chunks', () => {
    const m = renderer.match(/window\.api\.onPtyData\(\(sessionId, data\) => \{[\s\S]*?\}\)\)/);
    expect(m, 'onPtyData listener body must be findable').not.toBeNull();
    const body = m[0];
    // markSessionBusy must be gated by the chunk-substance filter so that
    // cursor blinks and idle redraws don't flicker the badge.
    expect(body).toMatch(/if\s*\(\s*chunkLooksLikeAgentActivity\(data\)\s*\)/);
    expect(body).toMatch(/markSessionBusy\(sessionId\)/);
    expect(body).not.toMatch(/sessionBusyState\.set\(sessionId,\s*true\)/);
  });

  it('pty:exit and pty:evicted handlers route through clearSessionBusy (no leaked timer)', () => {
    // pty:exit handler
    const exitM = renderer.match(/window\.api\.onPtyExit\([\s\S]*?\}\)\);/);
    expect(exitM, 'onPtyExit body must be findable').not.toBeNull();
    expect(exitM[0]).toMatch(/clearSessionBusy\(sessionId\)/);

    // pty:evicted handler
    const evictM = renderer.match(/window\.api\.onPtyEvicted\?\.\([\s\S]*?\}\);/);
    expect(evictM, 'onPtyEvicted body must be findable').not.toBeNull();
    expect(evictM[0]).toMatch(/clearSessionBusy\(sessionId\)/);
  });

  it('updateSessionBusyStates skips poll-based decay for sessions that have an active debounce timer (avoids racing the timer)', () => {
    const m = renderer.match(/async function updateSessionBusyStates[\s\S]*?\n\}/);
    expect(m, 'updateSessionBusyStates body must be findable').not.toBeNull();
    const body = m[0];
    expect(body).toMatch(/sessionBusyTimers\.has\(s\.id\)/);
  });

  it('updateSessionBusyStates only decays known-busy sessions and never elevates a session it has already set to false (preserves the timer as the sole busy=true authority, with one bootstrap exception)', () => {
    const m = renderer.match(/async function updateSessionBusyStates[\s\S]*?\n\}/);
    expect(m, 'updateSessionBusyStates body must be findable').not.toBeNull();
    const body = m[0];
    // The old "recentOutput → busy=true unconditionally" branch is gone.
    expect(body).not.toMatch(/if\s*\(\s*recentOutput\s*\)\s*\{\s*\/\/[^\n]*\n\s*sessionBusyState\.set\(s\.id,\s*true\)/);
    // The bootstrap path is gated on "the renderer hasn't recorded this
    // session yet" so it only fires once when the renderer attaches to an
    // already-running session.
    expect(body).toMatch(/!wasKnown\s*&&\s*recentOutput/);
    // Decay still consults IDLE_GRACE_POLLS so a single quiet poll cycle
    // doesn't immediately demote a session to Waiting.
    expect(body).toMatch(/IDLE_GRACE_POLLS/);
  });
});

describe('chunkLooksLikeAgentActivity filters ambient pty noise', () => {
  // Pull the helper out of the renderer source as standalone JS so we can
  // exercise it in isolation. The renderer module itself depends on xterm
  // + Electron globals that are painful to mock; the helper is a pure
  // function so we can lift its source out for unit testing.
  const ansiSrc = renderer.match(/const ANSI_ESCAPE_RE\s*=\s*\/[^;]*;/);
  const minSrc = renderer.match(/const BUSY_MIN_PRINTABLE_CHARS\s*=\s*\d+;/);
  const fnSrc = renderer.match(/function chunkLooksLikeAgentActivity\([\s\S]*?\n\}/);
  let chunkLooksLikeAgentActivity;
  if (ansiSrc && minSrc && fnSrc) {
    // eslint-disable-next-line no-new-func
    chunkLooksLikeAgentActivity = new Function(`${ansiSrc[0]}\n${minSrc[0]}\n${fnSrc[0]}\nreturn chunkLooksLikeAgentActivity;`)();
  }

  it('parses out of renderer source', () => {
    expect(chunkLooksLikeAgentActivity, 'helper must be liftable from renderer.js').toBeTypeOf('function');
  });

  it('returns false for empty / nullish chunks', () => {
    expect(chunkLooksLikeAgentActivity('')).toBe(false);
    expect(chunkLooksLikeAgentActivity(null)).toBe(false);
    expect(chunkLooksLikeAgentActivity(undefined)).toBe(false);
  });

  it('returns false for a bare cursor-blink ANSI sequence', () => {
    // Just hide/show cursor — pure ambient redraw.
    expect(chunkLooksLikeAgentActivity('\x1b[?25l\x1b[?25h')).toBe(false);
  });

  it('returns false for a clear-line + carriage-return idle redraw with no text', () => {
    expect(chunkLooksLikeAgentActivity('\x1b[2K\r')).toBe(false);
  });

  it('returns false for a 1–2 char keystroke echo', () => {
    expect(chunkLooksLikeAgentActivity('h')).toBe(false);
    expect(chunkLooksLikeAgentActivity('hi')).toBe(false);
  });

  it('returns true for a spinner frame that carries a status line', () => {
    // Real copilot CLI spinner: cursor move + glyph + " Reasoning..."
    expect(chunkLooksLikeAgentActivity('\x1b[2K\r⠋ Reasoning...')).toBe(true);
  });

  it('returns true for a streamed assistant response chunk', () => {
    expect(chunkLooksLikeAgentActivity('I think the answer is to refactor the helper')).toBe(true);
  });

  it('returns true for colored ANSI text with at least a few printable chars', () => {
    expect(chunkLooksLikeAgentActivity('\x1b[32mDone!\x1b[0m')).toBe(false); // "Done!" = 5 chars, just under
    expect(chunkLooksLikeAgentActivity('\x1b[32mFinished\x1b[0m')).toBe(true);
  });

  it('handles Buffer input by coercing to string', () => {
    const buf = Buffer.from('Reasoning about edge cases');
    expect(chunkLooksLikeAgentActivity(buf)).toBe(true);
  });
});

describe('folder icon uses inline monochrome SVG (not the yellow 📂 emoji)', () => {
  it('session card renders the cwd button with an SVG, not 📂', () => {
    // The card render block: find the cwdHtml line.
    const m = renderer.match(/cwdHtml\s*=\s*`[^`]*`/);
    expect(m, 'cwdHtml assignment must be findable').not.toBeNull();
    const tpl = m[0];
    expect(tpl).toMatch(/<svg/);
    expect(tpl).toMatch(/session-cwd-icon/);
    expect(tpl).not.toMatch(/📂/);
  });

  it('CSS sizes the SVG and uses currentColor on a dim default', () => {
    expect(css).toMatch(/\.session-cwd-icon\s*\{[\s\S]*?width:\s*1[1-4]px/);
    expect(css).toMatch(/\.session-cwd\s*\{[\s\S]*?color:\s*var\(--text-dim\)/);
    // Default opacity should be subtle (< 0.6) so the icon doesn't dominate.
    const m = css.match(/\.session-cwd\s*\{[\s\S]*?opacity:\s*0?\.(\d+)/);
    expect(m, 'session-cwd opacity rule must be findable').not.toBeNull();
    const opacity = Number('0.' + m[1]);
    expect(opacity).toBeLessThan(0.6);
  });
});

describe('Pending PR fires only for the latest assistant.message', () => {
  it('sidebar render uses session.lastAssistantHasPR (no resource-history scan)', () => {
    // The card render block: must consult the per-session boolean, NOT
    // session.resources.some(r => r.type === 'pr' ...).
    const m = renderer.match(/function renderSessionItem\([\s\S]*?\n\}/) ||
              renderer.match(/const isRunning = sessionAliveState\.has\(session\.id\);[\s\S]{0,400}deriveSessionState/);
    expect(m, 'session card render must be findable').not.toBeNull();
    expect(m[0]).toMatch(/session\.lastAssistantHasPR\s*===\s*true/);
  });

  it('patchSessionStateBadges and patchSessionStateBadgeForId both use lastAssistantHasPR', () => {
    const full = renderer.match(/function patchSessionStateBadges\(\)[\s\S]*?\n\}/);
    const one = renderer.match(/function patchSessionStateBadgeForId\([\s\S]*?\n\}/);
    expect(full, 'patchSessionStateBadges body must be findable').not.toBeNull();
    expect(one, 'patchSessionStateBadgeForId body must be findable').not.toBeNull();
    expect(full[0]).toMatch(/session\.lastAssistantHasPR\s*===\s*true/);
    expect(one[0]).toMatch(/session\.lastAssistantHasPR\s*===\s*true/);
  });

  it('renderer no longer references the old "any PR in resources" pattern for the status badge', () => {
    // The deprecated derivation looked like:
    //   session.resources && session.resources.some(r => r.type === 'pr' && ...)
    // — this should be gone from the badge-state derivation paths.
    expect(renderer).not.toMatch(/resources\.some\(r\s*=>\s*r\.type\s*===\s*['"]pr['"]\s*&&/);
  });
});

describe('SESSION CONTEXT bar has a fixed (not min-) height so fit() stays correct', () => {
  // Bug: when the bar was `min-height: 28px` it grew from 28px to ~32px when
  // populated with a prompt + the 22px copy button. fitAddon.fit() runs on
  // session switch BEFORE scheduleSessionPromptGhostRefresh populates the
  // bar — so the terminal viewport was computed against a 28px bar but the
  // actual rendered bar took ~32px, hiding the bottom row(s) of output
  // behind it. The user could not scroll to the very end of an agent reply.
  it('css pins .terminal-prompt-ghost to a fixed height (not min-height)', () => {
    const m = css.match(/\.terminal-prompt-ghost\s*\{[\s\S]*?\n\}/);
    expect(m, '.terminal-prompt-ghost rule must be findable').not.toBeNull();
    const body = m[0];
    expect(body, '.terminal-prompt-ghost must not use min-height (it grows when populated, breaking fit())').not.toMatch(/min-height\s*:/);
    expect(body).toMatch(/\bheight\s*:\s*32px\b/);
    // box-sizing: border-box keeps the 32px inclusive of padding so the
    // total layout footprint matches what fit() measured.
    expect(body).toMatch(/box-sizing\s*:\s*border-box/);
  });
});

describe('sidebar render skips destructive rebuild when nothing visible changed (anti-flicker)', () => {
  // Bug: pollSessionStatus runs every 3s and called refreshSessionList →
  // scheduleRenderSessionList → renderSessionList which did
  // `sessionList.innerHTML = ''` and rebuilt every card from scratch. The
  // result was a visible sidebar "blink" every 3 seconds. Now renderSessionList
  // computes a fingerprint of the visible state and short-circuits when it
  // matches the last render. Status badges + .running + active highlight are
  // still patched in place so they stay real-time.
  it('renderer declares a sidebar fingerprint cache var', () => {
    expect(renderer).toMatch(/let\s+_lastSidebarFingerprint\s*=\s*null/);
  });

  it('computeSidebarFingerprint depends on tab + search + sidebarCollapsed + groups + per-session visual state', () => {
    const m = renderer.match(/function computeSidebarFingerprint\([\s\S]*?\n\}/);
    expect(m, 'computeSidebarFingerprint body must be findable').not.toBeNull();
    const body = m[0];
    expect(body).toMatch(/currentSidebarTab\b/);
    expect(body).toMatch(/searchQuery\b/);
    expect(body).toMatch(/sidebarCollapsed\b/);
    expect(body).toMatch(/historyShowsAll\b/);
    expect(body).toMatch(/tabGroups\b/);
    // per-item: id, title, lastAssistantHasPR (Pending PR badge), tags, resources
    expect(body).toMatch(/s\.id\b/);
    expect(body).toMatch(/s\.title\b/);
    expect(body).toMatch(/s\.lastAssistantHasPR\b/);
    expect(body).toMatch(/s\.tags\b/);
    expect(body).toMatch(/s\.resources\b/);
  });

  it('renderSessionList short-circuits when the fingerprint is unchanged, but still patches badges + active highlight', () => {
    const m = renderer.match(/function renderSessionList\([\s\S]*?sessionList\.innerHTML\s*=\s*['"]['"]/);
    expect(m, 'renderSessionList early-return + clear-line must be findable').not.toBeNull();
    const body = m[0];
    // Compute the fingerprint after `displayed` is built
    expect(body).toMatch(/computeSidebarFingerprint\(displayed\)/);
    // Compare against the cached value
    expect(body).toMatch(/_lastSidebarFingerprint\b/);
    // The short-circuit branch must still patch in-place so status stays
    // real-time even when we skip the rebuild.
    expect(body).toMatch(/patchActiveHighlight/);
    expect(body).toMatch(/patchSessionStateBadges/);
  });

  it('patchSessionStateBadges keeps the .running class in sync (since the rebuild path is now skipped on aliveness-only changes)', () => {
    const m = renderer.match(/function patchSessionStateBadges\(\)[\s\S]*?\n\}/);
    expect(m, 'patchSessionStateBadges body must be findable').not.toBeNull();
    const body = m[0];
    // Must add .running when isRunning is true and the class is missing
    expect(body).toMatch(/isRunning\s*&&\s*!el\.classList\.contains\(['"]running['"]\)/);
    // Must remove .running when isRunning is false
    expect(body).toMatch(/!isRunning\s*&&\s*el\.classList\.contains\(['"]running['"]\)/);
  });

  it('patchSessionStateBadgeForId also patches .running (same reasoning, per-id path)', () => {
    const m = renderer.match(/function patchSessionStateBadgeForId\([\s\S]*?\n\}/);
    expect(m, 'patchSessionStateBadgeForId body must be findable').not.toBeNull();
    const body = m[0];
    expect(body).toMatch(/isRunning\s*&&\s*!el\.classList\.contains\(['"]running['"]\)/);
    expect(body).toMatch(/!isRunning\s*&&\s*el\.classList\.contains\(['"]running['"]\)/);
  });
});

describe('session switch is a single repaint (no double viewport sync)', () => {
  // Bug: switchToSession ran syncTerminalViewport(currentId) AND
  // scheduleTerminalViewportSync(currentId, ...) back-to-back. The first ran
  // immediately, the second ran ~20ms later in a queued rAF, producing a
  // visible double-paint flicker on every session switch (xterm canvas blink,
  // scrollbar jump, input box twitch). Keep only the scheduled one — it
  // already handles refreshSearch and runs in the next frame so the user
  // sees a single repaint.
  it('switchToSession does NOT call syncTerminalViewport synchronously alongside scheduleTerminalViewportSync', () => {
    const m = renderer.match(/function switchToSession\(sessionId\)[\s\S]*?\n\}/);
    expect(m, 'switchToSession body must be findable').not.toBeNull();
    const body = m[0];
    // The scheduled sync stays — that's the one repaint we want.
    expect(body).toMatch(/scheduleTerminalViewportSync\(currentId,\s*\{\s*refreshSearch:\s*true\s*\}\)/);
    // The redundant synchronous call must be gone.
    expect(body).not.toMatch(/^\s*syncTerminalViewport\(currentId\)\s*;/m);
  });
});

describe('side dot mirrors WORKING/WAITING status (green vs yellow), not just alive/dead', () => {
  // Bug: the `.session-item.running::after` dot was always green when a
  // session was alive, which made it meaningless — you couldn't tell from
  // the dot alone whether an agent was actively reasoning or sitting idle.
  // Now the dot reads from the same busy flag as the WORKING/WAITING badge:
  //   - .running.busy   → green (Working — agent is reasoning)
  //   - .running        → yellow (Waiting — agent is alive but idle)
  //   - (not .running)  → no dot (session is dead / history)
  // This makes the narrow-sidebar mode (where the badge text is clipped)
  // actually useful.
  it('CSS defaults .running::after to yellow and overrides to green only when .busy is also present', () => {
    // Default running state = yellow (Waiting)
    const yellowRule = css.match(/\.session-item\.running::after\s*\{[\s\S]*?\n\}/);
    expect(yellowRule, '.session-item.running::after rule must be findable').not.toBeNull();
    expect(yellowRule[0]).toMatch(/background\s*:\s*var\(--yellow\)/);
    expect(yellowRule[0]).toMatch(/box-shadow\s*:[^;]*var\(--yellow\)/);

    // .busy override = green (Working)
    const greenRule = css.match(/\.session-item\.running\.busy::after\s*\{[\s\S]*?\n\}/);
    expect(greenRule, '.session-item.running.busy::after override must be findable').not.toBeNull();
    expect(greenRule[0]).toMatch(/background\s*:\s*var\(--green\)/);
    expect(greenRule[0]).toMatch(/box-shadow\s*:[^;]*var\(--green\)/);
  });

  it('createSessionItem applies the .busy class on initial render when sessionBusyState is true', () => {
    const m = renderer.match(/function createSessionItem\([\s\S]*?\n\}/);
    expect(m, 'createSessionItem body must be findable').not.toBeNull();
    const body = m[0];
    // The .running class is applied when alive (pre-existing); now the .busy
    // class should be applied alongside it when the busy flag is set.
    expect(body).toMatch(/sessionBusyState\.get\(session\.id\)\s*===\s*true[\s\S]{0,40}classList\.add\(['"]busy['"]\)/);
  });

  it('patchSessionStateBadges keeps .busy in sync (add when running+busy, remove otherwise)', () => {
    const m = renderer.match(/function patchSessionStateBadges\(\)[\s\S]*?\n\}/);
    expect(m, 'patchSessionStateBadges body must be findable').not.toBeNull();
    const body = m[0];
    expect(body).toMatch(/isRunning\s*&&\s*isBusy\s*&&\s*!el\.classList\.contains\(['"]busy['"]\)/);
    expect(body).toMatch(/\(\s*!isRunning\s*\|\|\s*!isBusy\s*\)\s*&&\s*el\.classList\.contains\(['"]busy['"]\)/);
  });

  it('patchSessionStateBadgeForId also patches .busy (per-id path used by debounce timer)', () => {
    const m = renderer.match(/function patchSessionStateBadgeForId\([\s\S]*?\n\}/);
    expect(m, 'patchSessionStateBadgeForId body must be findable').not.toBeNull();
    const body = m[0];
    expect(body).toMatch(/isRunning\s*&&\s*isBusy\s*&&\s*!el\.classList\.contains\(['"]busy['"]\)/);
    expect(body).toMatch(/\(\s*!isRunning\s*\|\|\s*!isBusy\s*\)\s*&&\s*el\.classList\.contains\(['"]busy['"]\)/);
  });
});

describe('per-session red unread-notification badge removed (was noisy / not actionable)', () => {
  // Bug: the sidebar showed a red dot with a number on every session card
  // for unread notifications. Notifications fire on every session exit, so
  // the badge accumulated permanently until the user opened the bell menu
  // and clicked "mark all read". The global notification badge on the gear
  // icon already shows total unread, so the per-session badge was pure
  // duplication and noise.
  it('renderSessionList no longer enriches cards with .session-notification-badge', () => {
    expect(renderer).not.toMatch(/className\s*=\s*['"]session-notification-badge['"]/);
    expect(renderer).not.toMatch(/\.session-notification-badge/);
  });

  it('CSS rule for .session-notification-badge is removed', () => {
    expect(css).not.toMatch(/\.session-notification-badge\s*\{/);
  });

  it('the collapsed-sidebar hide rule for the badge is also cleaned up', () => {
    expect(css).not.toMatch(/#sidebar\.collapsed[\s\S]*?\.session-notification-badge/);
  });
});

