// Tiny stack VM: a faithful interpreter of make.fun's tiny stack ISA v1.
// One run answers every instance in /input/<id>/, writing
// /output/<id>/stdout.bin + exit.txt. Node 22, erasable TS only.
import { mkdirSync as mk, readdirSync as ls, readFileSync as rf, writeFileSync as wf } from 'node:fs';
import { join as j } from 'node:path';

// Opcode table [byte, immediate bytes, pops, pushes], ids in this order:
// HALT PUSH8 PUSH32 POP DUP SWAP OVER ROT ADD SUB MUL DIV MOD DIVU MODU NEG
// AND OR XOR NOT SHL SHR SHRU EQ LT LTU JMP JZ JNZ CALL RET LOAD STORE
// PRINT PUTC IN EXIT.
const T=[0,0,0,0,1,1,0,1,2,4,0,1,3,0,1,0,4,0,1,2,5,0,2,2,6,0,2,3,7,0,3,3,16,0,2,1,17,0,2,1,18,0,2,1,19,0,2,1,20,0,2,1,21,0,2,1,22,0,2,1,23,0,1,1,24,0,2,1,25,0,2,1,26,0,2,1,27,0,1,1,28,0,2,1,29,0,2,1,30,0,2,1,32,0,2,1,33,0,2,1,34,0,2,1,48,2,0,0,49,2,1,0,50,2,1,0,51,2,0,0,52,0,0,0,64,0,1,1,65,0,2,0,80,0,1,0,81,0,1,0,82,0,0,1,83,0,1,0];
const IL=new Int8Array(37),PO=new Int8Array(37),PU=new Int8Array(37);
const ID=new Int8Array(256).fill(-1);
for(let k=0;k<T.length;k+=4){const id=k>>2;ID[T[k]]=id;IL[id]=T[k+1];PO[id]=T[k+2];PU[id]=T[k+3];}
const enc=new TextEncoder();

// Runs one program on its input, returning [output bytes, exit code]. A trap
// ends the program at once with the trap's code, keeping earlier output.
function run(p:Uint8Array,inp:Uint8Array):[Uint8Array,number]{
  const n=p.length;
  // Decode every byte offset once: A is the opcode id (-1 unknown opcode,
  // -2 immediate cut off by the end), V its immediate value.
  const A=new Int8Array(n),V=new Int32Array(n);
  for(let i=0;i<n;i++){
    const id=ID[p[i]];
    if(id<0){A[i]=-1;continue;}
    const imm=IL[id];
    if(i+imm>=n){A[i]=-2;continue;}
    A[i]=id;
    if(imm===1)V[i]=(p[i+1]<<24)>>24;
    else if(imm===4)V[i]=p[i+1]|(p[i+2]<<8)|(p[i+3]<<16)|(p[i+4]<<24);
    else if(imm===2)V[i]=id===29?p[i+1]|(p[i+2]<<8):((p[i+1]|(p[i+2]<<8))<<16)>>16;
  }
  const D=new Int32Array(256),C=new Int32Array(64),M=new Int32Array(256);
  const out=new Uint8Array(65536);
  let sp=0,csp=0,pc=0,steps=0,olen=0,ip=0;
  const done=(code:number):[Uint8Array,number]=>[out.slice(0,olen),code];
  for(;;){
    if(steps===1000000)return done(10);
    if(pc<0||pc>=n)return done(9);
    const id=A[pc];
    if(id<0)return done(id===-1?5:9);
    steps++;
    const nx=pc+1+IL[id],v=V[pc];
    if(sp<PO[id])return done(2);
    if(sp-PO[id]+PU[id]>256)return done(3);
    pc=nx;
    switch(id){
      case 0:return done(0);
      case 1:case 2:D[sp++]=v;break;
      case 3:sp--;break;
      case 4:D[sp]=D[sp-1];sp++;break;
      case 5:{const t=D[sp-1];D[sp-1]=D[sp-2];D[sp-2]=t;break;}
      case 6:D[sp]=D[sp-2];sp++;break;
      case 7:{const a=D[sp-3];D[sp-3]=D[sp-2];D[sp-2]=D[sp-1];D[sp-1]=a;break;}
      case 15:D[sp-1]=-D[sp-1]|0;break;
      case 19:D[sp-1]=~D[sp-1];break;
      case 8:case 9:case 10:case 11:case 12:case 13:case 14:case 16:
      case 17:case 18:case 20:case 21:case 22:case 23:case 24:case 25:{
        const b=D[sp-1],a=D[sp-2];
        let r:number;
        switch(id){
          case 8:r=(a+b)|0;break;
          case 9:r=(a-b)|0;break;
          case 10:r=Math.imul(a,b);break;
          case 11:if(b===0)return done(4);r=a===-2147483648&&b===-1?a:(a/b)|0;break;
          case 12:if(b===0)return done(4);r=b===-1?0:(a%b)|0;break;
          case 13:if(b===0)return done(4);r=Math.floor((a>>>0)/(b>>>0))|0;break;
          case 14:if(b===0)return done(4);r=((a>>>0)%(b>>>0))|0;break;
          case 16:r=a&b;break;
          case 17:r=a|b;break;
          case 18:r=a^b;break;
          case 20:r=a<<(b&31);break;
          case 21:r=a>>(b&31);break;
          case 22:r=(a>>>(b&31))|0;break;
          case 23:r=a===b?1:0;break;
          case 24:r=a<b?1:0;break;
          default:r=(a>>>0)<(b>>>0)?1:0;
        }
        sp-=2;D[sp++]=r;
        break;
      }
      case 26:pc=nx+v;break;
      case 27:if(D[--sp]===0)pc=nx+v;break;
      case 28:if(D[--sp]!==0)pc=nx+v;break;
      case 29:
        if(csp===64)return done(7);
        C[csp++]=nx;pc=v;break;
      case 30:
        if(csp===0)return done(8);
        pc=C[--csp];break;
      case 31:{
        const addr=D[sp-1];
        if(addr<0||addr>=256)return done(6);
        D[sp-1]=M[addr];break;
      }
      case 32:{
        const addr=D[sp-1],w=D[sp-2];
        if(addr<0||addr>=256)return done(6);
        sp-=2;M[addr]=w;break;
      }
      case 33:{
        const bytes=enc.encode(String(D[sp-1]));
        if(olen+bytes.length>65536)return done(11);
        sp--;out.set(bytes,olen);olen+=bytes.length;break;
      }
      case 34:
        if(olen+1>65536)return done(11);
        out[olen++]=D[--sp]&255;break;
      case 35:D[sp++]=ip<inp.length?inp[ip++]:-1;break;
      default:return done(D[--sp]&255);
    }
  }
}

const I=process.env.MAKEFUN_INPUT_DIR??'/input';
const O=process.env.MAKEFUN_OUTPUT_DIR??'/output';
for(const id of ls(I).sort()){
  const [o,c]=run(new Uint8Array(rf(j(I,id,'program.bin'))),new Uint8Array(rf(j(I,id,'input.bin'))));
  mk(j(O,id),{recursive:true});
  wf(j(O,id,'stdout.bin'),o);
  wf(j(O,id,'exit.txt'),c+'\n');
}
