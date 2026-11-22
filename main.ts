// Tiny stack VM: a from-scratch interpreter for make.fun's tiny stack ISA v1.
// One run answers every instance in /input/<id>/, writing stdout.bin + exit.txt.
// Node 22, erasable TS only. Trap codes: 2 underflow, 3 overflow, 4 div by zero,
// 5 bad opcode, 6 bad memory address, 7 call depth, 8 empty return, 9 bad pc,
// 10 step limit, 11 output limit.
import { mkdirSync as mk, readdirSync as ls, readFileSync as rf, writeFileSync as wf } from 'node:fs';
import { join as j } from 'node:path';
const text = new TextEncoder();
const BIN: Record<number, (a: number, b: number) => number | null> = {
  0x10: (a, b) => (a + b) | 0,
  0x11: (a, b) => (a - b) | 0,
  0x12: (a, b) => Math.imul(a, b),
  0x13: (a, b) => (b === 0 ? null : a === -2147483648 && b === -1 ? a : (a / b) | 0),
  0x14: (a, b) => (b === 0 ? null : b === -1 ? 0 : (a % b) | 0),
  0x15: (a, b) => (b === 0 ? null : Math.floor((a >>> 0) / (b >>> 0)) | 0),
  0x16: (a, b) => (b === 0 ? null : ((a >>> 0) % (b >>> 0)) | 0),
  0x18: (a, b) => a & b,
  0x19: (a, b) => a | b,
  0x1a: (a, b) => a ^ b,
  0x1c: (a, b) => a << (b & 31),
  0x1d: (a, b) => a >> (b & 31),
  0x1e: (a, b) => (a >>> (b & 31)) | 0,
  0x20: (a, b) => (a === b ? 1 : 0),
  0x21: (a, b) => (a < b ? 1 : 0),
  0x22: (a, b) => ((a >>> 0) < (b >>> 0) ? 1 : 0),
};
export function execute(prog: Uint8Array, input: Uint8Array) {
  const stack = new Int32Array(256);
  const returns = new Int32Array(64);
  const memory = new Int32Array(256);
  const out = new Uint8Array(65536);
  let sp = 0;
  let rp = 0;
  let pc = 0;
  let steps = 0;
  let produced = 0;
  let consumed = 0;
  const finish = (code: number) => ({ bytes: out.slice(0, produced), code });
  for (;;) {
    if (steps === 1000000) return finish(10);
    if (pc < 0 || pc >= prog.length) return finish(9);
    const op = prog[pc];
    const immLen = op === 0x01 ? 1 : op === 0x02 ? 4 : op >= 0x30 && op <= 0x33 ? 2 : 0;
    if (pc + immLen >= prog.length) return finish(9);
    steps += 1;
    const after = pc + 1 + immLen;
    pc = after;
    switch (op) {
      case 0x00: 
        return finish(0);
      case 0x01: { 
        if (sp + 1 > 256) return finish(3);
        stack[sp++] = (prog[after - 1] << 24) >> 24;
        break;
      }
      case 0x02: { 
        if (sp + 1 > 256) return finish(3);
        stack[sp++] =
          prog[after - 4] |
          (prog[after - 3] << 8) |
          (prog[after - 2] << 16) |
          (prog[after - 1] << 24);
        break;
      }
      case 0x03: 
        if (sp < 1) return finish(2);
        sp -= 1;
        break;
      case 0x04: 
        if (sp < 1) return finish(2);
        if (sp + 1 > 256) return finish(3);
        stack[sp] = stack[sp - 1];
        sp += 1;
        break;
      case 0x05: { 
        if (sp < 2) return finish(2);
        const top = stack[sp - 1];
        stack[sp - 1] = stack[sp - 2];
        stack[sp - 2] = top;
        break;
      }
      case 0x06: 
        if (sp < 2) return finish(2);
        if (sp + 1 > 256) return finish(3);
        stack[sp] = stack[sp - 2];
        sp += 1;
        break;
      case 0x07: { 
        if (sp < 3) return finish(2);
        const bottom = stack[sp - 3];
        stack[sp - 3] = stack[sp - 2];
        stack[sp - 2] = stack[sp - 1];
        stack[sp - 1] = bottom;
        break;
      }
      case 0x17: 
        if (sp < 1) return finish(2);
        stack[sp - 1] = -stack[sp - 1] | 0;
        break;
      case 0x1b: 
        if (sp < 1) return finish(2);
        stack[sp - 1] = ~stack[sp - 1];
        break;
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15:
      case 0x16: case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d:
      case 0x1e: case 0x20: case 0x21: case 0x22: {
        if (sp < 2) return finish(2);
        const r = BIN[op]!(stack[sp - 2], stack[sp - 1]);
        if (r === null) return finish(4);
        sp -= 2;
        stack[sp++] = r;
        break;
      }
      case 0x30: 
      case 0x31: 
      case 0x32: { 
        const offset = ((prog[after - 2] | (prog[after - 1] << 8)) << 16) >> 16;
        let take = true;
        if (op !== 0x30) {
          if (sp < 1) return finish(2);
          const v = stack[--sp];
          take = op === 0x31 ? v === 0 : v !== 0;
        }
        if (take) pc = after + offset;
        break;
      }
      case 0x33: 
        if (rp === 64) return finish(7);
        returns[rp++] = after;
        pc = prog[after - 2] | (prog[after - 1] << 8);
        break;
      case 0x34: 
        if (rp === 0) return finish(8);
        pc = returns[--rp];
        break;
      case 0x40: { 
        if (sp < 1) return finish(2);
        const addr = stack[sp - 1];
        if (addr < 0 || addr >= 256) return finish(6);
        stack[sp - 1] = memory[addr];
        break;
      }
      case 0x41: { 
        if (sp < 2) return finish(2);
        const addr = stack[sp - 1];
        const value = stack[sp - 2];
        if (addr < 0 || addr >= 256) return finish(6);
        sp -= 2;
        memory[addr] = value;
        break;
      }
      case 0x50: { 
        if (sp < 1) return finish(2);
        const bytes = text.encode(String(stack[sp - 1]));
        if (produced + bytes.length > 65536) return finish(11);
        sp -= 1;
        out.set(bytes, produced);
        produced += bytes.length;
        break;
      }
      case 0x51: 
        if (sp < 1) return finish(2);
        if (produced + 1 > 65536) return finish(11);
        out[produced++] = stack[--sp] & 255;
        break;
      case 0x52: { 
        if (sp + 1 > 256) return finish(3);
        stack[sp++] = consumed < input.length ? input[consumed++] : -1;
        break;
      }
      default: 
        if (op !== 0x53) return finish(5);
        if (sp < 1) return finish(2);
        return finish(stack[--sp] & 255);
    }
  }
}
const INPUT_DIR = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUTPUT_DIR = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of ls(INPUT_DIR).sort()) {
  const result = execute(
    new Uint8Array(rf(j(INPUT_DIR, id, 'program.bin'))),
    new Uint8Array(rf(j(INPUT_DIR, id, 'input.bin'))),
  );
  mk(j(OUTPUT_DIR, id), { recursive: true });
  wf(j(OUTPUT_DIR, id, 'stdout.bin'), result.bytes);
  wf(j(OUTPUT_DIR, id, 'exit.txt'), result.code + '\n');
}
