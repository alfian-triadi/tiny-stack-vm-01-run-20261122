// Tiny stack VM (ISA v1) for make.fun tiny-stack-vm-01: a faithful, fast
// interpreter of the ISA, following the reference VM (vm.mjs) rule for
// rule — wrapping 32-bit arithmetic, 256-value stack, 64-deep call stack,
// 256 words of memory, all ten traps with their own exit codes, the
// 1,000,000-step and 65,536-byte output limits. Deterministic: no clock,
// no environment, no network. Answers every instance of a set in one run.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// Opcode tables: immediate bytes, values popped, values pushed, known flag.
const IMM = new Uint8Array(256);
const POP = new Uint8Array(256);
const PSH = new Uint8Array(256);
const OK = new Uint8Array(256);
const def = (o: number, i: number, p: number, s: number): void => { IMM[o] = i; POP[o] = p; PSH[o] = s; OK[o] = 1; };
def(0x00, 0, 0, 0); def(0x01, 1, 0, 1); def(0x02, 4, 0, 1);
def(0x03, 0, 1, 0); def(0x04, 0, 1, 2); def(0x05, 0, 2, 2);
def(0x06, 0, 2, 3); def(0x07, 0, 3, 3);
for (let o = 0x10; o <= 0x16; o++) def(o, 0, 2, 1);
def(0x17, 0, 1, 1);
for (let o = 0x18; o <= 0x1e; o++) def(o, 0, 2, 1);
def(0x1b, 0, 1, 1);
for (let o = 0x20; o <= 0x22; o++) def(o, 0, 2, 1);
def(0x30, 2, 0, 0); def(0x31, 2, 1, 0); def(0x32, 2, 1, 0);
def(0x33, 2, 0, 0); def(0x34, 0, 0, 0);
def(0x40, 0, 1, 1); def(0x41, 0, 2, 0);
def(0x50, 0, 1, 0); def(0x51, 0, 1, 0); def(0x52, 0, 0, 1); def(0x53, 0, 1, 0);

const DIG = new Uint8Array(12); // scratch: decimal digits, reversed
// Writes the decimal of v at out[ol..]; returns the new length, or -1 when
// it would pass the 65,536-byte output limit (the trap writes nothing).
function writeDec(out: Uint8Array, ol: number, v: number): number {
  let n = 0;
  let neg = false;
  if (v < 0) { neg = true; v = -v; } // -(-2147483648) is 2147483648, exact
  if (v === 0) DIG[n++] = 48;
  else while (v > 0) { DIG[n++] = 48 + (v % 10); v = Math.floor(v / 10); }
  const len = n + (neg ? 1 : 0);
  if (ol + len > 65536) return -1;
  if (neg) out[ol++] = 45;
  for (let k = n - 1; k >= 0; k--) out[ol++] = DIG[k];
  return ol;
}

function run(p: Uint8Array, inp: Uint8Array): { out: Uint8Array; len: number; code: number } {
  const D = new Int32Array(256);
  let sp = 0;
  const C = new Int32Array(64);
  let cp = 0;
  const M = new Int32Array(256);
  const out = new Uint8Array(65536);
  let ol = 0;
  let ip = 0;
  let pc = 0;
  let steps = 0;
  const n = p.length;
  const done = (code: number): { out: Uint8Array; len: number; code: number } => ({ out, len: ol, code });
  for (;;) {
    if (steps === 1000000) return done(10);
    if (pc < 0 || pc >= n) return done(9);
    const op = p[pc];
    if (!OK[op]) return done(5);
    const imm = IMM[op];
    if (pc + imm >= n) return done(9);
    steps++;
    const nx = pc + 1 + imm;
    const pops = POP[op];
    const push = PSH[op];
    if (sp < pops) return done(2);
    if (sp - pops + push > 256) return done(3);
    pc = nx;
    switch (op) {
      case 0x00: return done(0);
      case 0x01: D[sp++] = (p[nx - 1] << 24) >> 24; break;
      case 0x02: D[sp++] = p[nx - 4] | (p[nx - 3] << 8) | (p[nx - 2] << 16) | (p[nx - 1] << 24); break;
      case 0x03: sp--; break;
      case 0x04: D[sp] = D[sp - 1]; sp++; break;
      case 0x05: { const t = D[sp - 1]; D[sp - 1] = D[sp - 2]; D[sp - 2] = t; break; }
      case 0x06: D[sp] = D[sp - 2]; sp++; break;
      case 0x07: { const a = D[sp - 3]; D[sp - 3] = D[sp - 2]; D[sp - 2] = D[sp - 1]; D[sp - 1] = a; break; }
      case 0x17: D[sp - 1] = -D[sp - 1] | 0; break;
      case 0x1b: D[sp - 1] = ~D[sp - 1]; break;
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15: case 0x16:
      case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d: case 0x1e:
      case 0x20: case 0x21: case 0x22: {
        const b = D[sp - 1];
        const a = D[sp - 2];
        let r: number;
        if (op === 0x10) r = (a + b) | 0;
        else if (op === 0x11) r = (a - b) | 0;
        else if (op === 0x12) r = Math.imul(a, b);
        else if (op === 0x13) {
          if (b === 0) return done(4);
          r = a === -2147483648 && b === -1 ? a : (a / b) | 0;
        } else if (op === 0x14) {
          if (b === 0) return done(4);
          r = b === -1 ? 0 : (a % b) | 0;
        } else if (op === 0x15) {
          if (b === 0) return done(4);
          r = Math.floor((a >>> 0) / (b >>> 0)) | 0;
        } else if (op === 0x16) {
          if (b === 0) return done(4);
          r = ((a >>> 0) % (b >>> 0)) | 0;
        } else if (op === 0x18) r = a & b;
        else if (op === 0x19) r = a | b;
        else if (op === 0x1a) r = a ^ b;
        else if (op === 0x1c) r = a << (b & 31);
        else if (op === 0x1d) r = a >> (b & 31);
        else if (op === 0x1e) r = (a >>> (b & 31)) | 0;
        else if (op === 0x20) r = a === b ? 1 : 0;
        else if (op === 0x21) r = a < b ? 1 : 0;
        else r = (a >>> 0) < (b >>> 0) ? 1 : 0;
        sp -= 2;
        D[sp++] = r;
        break;
      }
      case 0x30: case 0x31: case 0x32: {
        const rel = ((p[nx - 2] | (p[nx - 1] << 8)) << 16) >> 16;
        let take = true;
        if (op !== 0x30) {
          const v = D[--sp];
          take = op === 0x31 ? v === 0 : v !== 0;
        }
        if (take) pc = nx + rel;
        break;
      }
      case 0x33:
        if (cp === 64) return done(7);
        C[cp++] = nx;
        pc = p[nx - 2] | (p[nx - 1] << 8);
        break;
      case 0x34:
        if (cp === 0) return done(8);
        pc = C[--cp];
        break;
      case 0x40: {
        const addr = D[sp - 1];
        if (addr < 0 || addr >= 256) return done(6);
        D[sp - 1] = M[addr];
        break;
      }
      case 0x41: {
        const addr = D[sp - 1];
        const v = D[sp - 2];
        if (addr < 0 || addr >= 256) return done(6);
        sp -= 2;
        M[addr] = v;
        break;
      }
      case 0x50: {
        const nl = writeDec(out, ol, D[sp - 1]);
        if (nl < 0) return done(11);
        sp--;
        ol = nl;
        break;
      }
      case 0x51:
        if (ol + 1 > 65536) return done(11);
        out[ol++] = D[--sp] & 255;
        break;
      case 0x52: D[sp++] = ip < inp.length ? inp[ip++] : -1; break;
      case 0x53: return done(D[--sp] & 255);
    }
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  const r = run(
    new Uint8Array(readFileSync(join(I, id, 'program.bin'))),
    new Uint8Array(readFileSync(join(I, id, 'input.bin'))),
  );
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), r.out.subarray(0, r.len));
  writeFileSync(join(O, id, 'exit.txt'), `${r.code}\n`);
}
