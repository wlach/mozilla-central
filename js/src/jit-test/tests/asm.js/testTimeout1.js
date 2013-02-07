// |jit-test| exitstatus: 6;

load(libdir + "asm.js");

timeout(.1);
asmLink(asmCompile(USE_ASM + "function f() {} function g() { while(1) { f() } } return g"))();
assertEq(true, false);
