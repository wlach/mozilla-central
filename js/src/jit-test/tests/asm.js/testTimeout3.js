// |jit-test| exitstatus: 6;

load(libdir + "asm.js");

timeout(.1);
asmLink(asmCompile(USE_ASM + "function f(i) { i=i|0; if (!i) return; f((i-1)|0); f((i-1)|0); f((i-1)|0); f((i-1)|0); f((i-1)|0); } return f"))(100);
assertEq(true, false);
