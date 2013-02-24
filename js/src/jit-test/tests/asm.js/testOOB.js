load(libdir + "asm.js");

// constants
var buf = new ArrayBuffer(8);
assertEq(asmLink(asmCompile('glob', 'imp', 'b', USE_ASM + 'var arr=new glob.Int8Array(b); function f() {return arr[0x7fffffff]|0 } return f'), this, null, buf)(), 0);
assertEq(asmLink(asmCompile('glob', 'imp', 'b', USE_ASM + 'var arr=new glob.Int8Array(b); function f() {return arr[0x80000000]|0 } return f'), this, null, buf)(), 0);
assertEq(asmLink(asmCompile('glob', 'imp', 'b', USE_ASM + 'var arr=new glob.Int8Array(b); function f() {return arr[0x8fffffff]|0 } return f'), this, null, buf)(), 0);
assertEq(asmLink(asmCompile('glob', 'imp', 'b', USE_ASM + 'var arr=new glob.Int8Array(b); function f() {return arr[0xffffffff]|0 } return f'), this, null, buf)(), 0);
assertEq(asmLink(asmCompile('glob', 'imp', 'b', USE_ASM + 'var arr=new glob.Int8Array(b); function f() {return arr[-1]|0 } return f'), this, null, buf)(), 0);
assertEq(asmLink(asmCompile('glob', 'imp', 'b', USE_ASM + 'var arr=new glob.Int8Array(b); function f() {return arr[-2]|0 } return f'), this, null, buf)(), 0);
assertAsmTypeFail('glob', 'imp', 'b', USE_ASM + 'var arr=new glob.Int16Array(b); function f() {return arr[-1]|0 } return f');
assertAsmTypeFail('glob', 'imp', 'b', USE_ASM + 'var arr=new glob.Int32Array(b); function f() {return arr[-2]|0 } return f');

function testInt(ctor, shift, sizes) {
    for (var bytes of sizes) {
        var ab = new ArrayBuffer(bytes);
        var arr = new ctor(ab);
        for (var i = 0; i < arr.length; i++)
            arr[i] = i;
        var f = asmLink(asmCompile('glob', 'imp', 'b', USE_ASM + 'var arr=new glob.' + ctor.name + '(b); function f(i) {i=i|0; return arr[i>>' + shift + ']|0 } return f'), this, null, ab);
        for (var i = 0; i < 2*bytes; i++)
            assertEq(f(i), arr[i>>shift]|0);

        for (var i of [-Math.pow(2,31), Math.pow(2,31)-1, Math.pow(2,32)]) {
            for (var j of [-8,-5,-4,-1,0,1,4,5,8])
                assertEq(f(i+j), arr[(i+j)>>shift]|0);
        }

        var f = asmLink(asmCompile('glob', 'imp', 'b', USE_ASM + 'var arr=new glob.' + ctor.name + '(b); function f(i,j) {i=i|0;j=j|0; arr[i>>' + shift + '] = j } return f'), this, null, ab);
        for (var i = 0; i < 2*bytes; i++) {
            var v = arr[i>>shift]|0;
            arr[i>>shift] = 0;
            f(i, v);
            assertEq(arr[i>>shift]|0, v);
        }

        for (var i of [-Math.pow(2,31), Math.pow(2,31)-1, Math.pow(2,32)]) {
            for (var j of [-8,-5,-4,-1,0,1,4,5,8]) {
                var v = arr[(i+j)>>shift]|0;
                arr[(i+j)>>shift] = 0;
                f(i+j, v);
                assertEq(arr[(i+j)>>shift]|0, v);
            }
        }
    }
}

testInt(Int8Array, 0, [1, 2, 13, 43, 250]);
testInt(Uint8Array, 0, [1, 2, 13, 43, 250]);
testInt(Int16Array, 1, [2, 14, 44, 250]);
testInt(Uint16Array, 1, [2, 14, 44, 250]);
testInt(Int32Array, 2, [4, 16, 44, 252]);
testInt(Uint32Array, 2, [4, 16, 44, 252]);

function testFloat(ctor, shift, sizes) {
    for (var bytes of sizes) {
        var ab = new ArrayBuffer(bytes);
        var arr = new ctor(ab);
        for (var i = 0; i < arr.length; i++)
            arr[i] = i;
        var f = asmLink(asmCompile('glob', 'imp', 'b', USE_ASM + 'var arr=new glob.' + ctor.name + '(b); function f(i) {i=i|0; return +arr[i>>' + shift + '] } return f'), this, null, ab);
        for (var i = 0; i < 2*bytes; i++)
            assertEq(f(i), +arr[i>>shift]);

        for (var i of [-Math.pow(2,31), Math.pow(2,31)-1, Math.pow(2,32)]) {
            for (var j of [-8,-5,-4,-1,0,1,4,5,8])
                assertEq(f(i+j), +arr[(i+j)>>shift]);
        }

        var f = asmLink(asmCompile('glob', 'imp', 'b', USE_ASM + 'var arr=new glob.' + ctor.name + '(b); function f(i,j) {i=i|0;j=+j; arr[i>>' + shift + '] = j } return f'), this, null, ab);
        for (var i = 0; i < 2*bytes; i++) {
            var v = +arr[i>>shift];
            arr[i>>shift] = 0;
            f(i, v);
            assertEq(+arr[i>>shift], v);
        }

        for (var i of [-Math.pow(2,31), Math.pow(2,31)-1, Math.pow(2,32)]) {
            for (var j of [-8,-5,-4,-1,0,1,4,5,8]) {
                var v = +arr[(i+j)>>shift];
                arr[(i+j)>>shift] = 0;
                f(i+j, v);
                assertEq(+arr[(i+j)>>shift], v);
            }
        }
    }
}

testFloat(Float32Array, 2, [4, 16, 44, 252]);
testFloat(Float64Array, 3, [8, 16, 48, 256]);
