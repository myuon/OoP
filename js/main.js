"use strict";
// This object will hold all exports.
var Haste = {};

/* Thunk
   Creates a thunk representing the given closure.
   If the non-updatable flag is undefined, the thunk is updatable.
*/
function T(f, nu) {
    this.f = f;
    if(nu === undefined) {
        this.x = __updatable;
    }
}

/* Hint to optimizer that an imported symbol is strict. */
function __strict(x) {return x}

// A tailcall.
function F(f) {
    this.f = f;
}

// A partially applied function. Invariant: members are never thunks.
function PAP(f, args) {
    this.f = f;
    this.args = args;
    this.arity = f.length - args.length;
}

// Special object used for blackholing.
var __blackhole = {};

// Used to indicate that an object is updatable.
var __updatable = {};

/* Generic apply.
   Applies a function *or* a partial application object to a list of arguments.
   See https://ghc.haskell.org/trac/ghc/wiki/Commentary/Rts/HaskellExecution/FunctionCalls
   for more information.
*/
function A(f, args) {
    while(true) {
        f = E(f);
        if(f instanceof F) {
            f = E(B(f));
        }
        if(f instanceof PAP) {
            // f is a partial application
            if(args.length == f.arity) {
                // Saturated application
                return f.f.apply(null, f.args.concat(args));
            } else if(args.length < f.arity) {
                // Application is still unsaturated
                return new PAP(f.f, f.args.concat(args));
            } else {
                // Application is oversaturated; 
                var f2 = f.f.apply(null, f.args.concat(args.slice(0, f.arity)));
                args = args.slice(f.arity);
                f = B(f2);
            }
        } else if(f instanceof Function) {
            if(args.length == f.length) {
                return f.apply(null, args);
            } else if(args.length < f.length) {
                return new PAP(f, args);
            } else {
                var f2 = f.apply(null, args.slice(0, f.length));
                args = args.slice(f.length);
                f = B(f2);
            }
        } else {
            return f;
        }
    }
}

/* Eval
   Evaluate the given thunk t into head normal form.
   If the "thunk" we get isn't actually a thunk, just return it.
*/
function E(t) {
    if(t instanceof T) {
        if(t.f !== __blackhole) {
            if(t.x === __updatable) {
                var f = t.f;
                t.f = __blackhole;
                t.x = f();
            } else {
                return t.f();
            }
        }
        return t.x;
    } else {
        return t;
    }
}

/* Bounce
   Bounce on a trampoline for as long as we get a function back.
*/
function B(f) {
    while(f instanceof F) {
        var fun = f.f;
        f.f = __blackhole;
        f = fun();
    }
    return f;
}

// Export Haste, A, B and E. Haste because we need to preserve exports, A, B
// and E because they're handy for Haste.Foreign.
if(!window) {
    var window = {};
}
window['Haste'] = Haste;
window['A'] = A;
window['E'] = E;
window['B'] = B;


/* Throw an error.
   We need to be able to use throw as an exception so we wrap it in a function.
*/
function die(err) {
    throw E(err);
}

function quot(a, b) {
    return (a-a%b)/b;
}

function quotRemI(a, b) {
    return [0, (a-a%b)/b, a%b];
}

// 32 bit integer multiplication, with correct overflow behavior
// note that |0 or >>>0 needs to be applied to the result, for int and word
// respectively.
if(Math.imul) {
    var imul = Math.imul;
} else {
    var imul = function(a, b) {
        // ignore high a * high a as the result will always be truncated
        var lows = (a & 0xffff) * (b & 0xffff); // low a * low b
        var aB = (a & 0xffff) * (b & 0xffff0000); // low a * high b
        var bA = (a & 0xffff0000) * (b & 0xffff); // low b * high a
        return lows + aB + bA; // sum will not exceed 52 bits, so it's safe
    }
}

function addC(a, b) {
    var x = a+b;
    return [0, x & 0xffffffff, x > 0x7fffffff];
}

function subC(a, b) {
    var x = a-b;
    return [0, x & 0xffffffff, x < -2147483648];
}

function sinh (arg) {
    return (Math.exp(arg) - Math.exp(-arg)) / 2;
}

function tanh (arg) {
    return (Math.exp(arg) - Math.exp(-arg)) / (Math.exp(arg) + Math.exp(-arg));
}

function cosh (arg) {
    return (Math.exp(arg) + Math.exp(-arg)) / 2;
}

function isFloatFinite(x) {
    return isFinite(x);
}

function isDoubleFinite(x) {
    return isFinite(x);
}

function err(str) {
    die(toJSStr(str));
}

/* unpackCString#
   NOTE: update constructor tags if the code generator starts munging them.
*/
function unCStr(str) {return unAppCStr(str, [0]);}

function unFoldrCStr(str, f, z) {
    var acc = z;
    for(var i = str.length-1; i >= 0; --i) {
        acc = B(A(f, [str.charCodeAt(i), acc]));
    }
    return acc;
}

function unAppCStr(str, chrs) {
    var i = arguments[2] ? arguments[2] : 0;
    if(i >= str.length) {
        return E(chrs);
    } else {
        return [1,str.charCodeAt(i),new T(function() {
            return unAppCStr(str,chrs,i+1);
        })];
    }
}

function charCodeAt(str, i) {return str.charCodeAt(i);}

function fromJSStr(str) {
    return unCStr(E(str));
}

function toJSStr(hsstr) {
    var s = '';
    for(var str = E(hsstr); str[0] == 1; str = E(str[2])) {
        s += String.fromCharCode(E(str[1]));
    }
    return s;
}

// newMutVar
function nMV(val) {
    return ({x: val});
}

// readMutVar
function rMV(mv) {
    return mv.x;
}

// writeMutVar
function wMV(mv, val) {
    mv.x = val;
}

// atomicModifyMutVar
function mMV(mv, f) {
    var x = B(A(f, [mv.x]));
    mv.x = x[1];
    return x[2];
}

function localeEncoding() {
    var le = newByteArr(5);
    le['v']['i8'][0] = 'U'.charCodeAt(0);
    le['v']['i8'][1] = 'T'.charCodeAt(0);
    le['v']['i8'][2] = 'F'.charCodeAt(0);
    le['v']['i8'][3] = '-'.charCodeAt(0);
    le['v']['i8'][4] = '8'.charCodeAt(0);
    return le;
}

var isDoubleNaN = isNaN;
var isFloatNaN = isNaN;

function isDoubleInfinite(d) {
    return (d === Infinity);
}
var isFloatInfinite = isDoubleInfinite;

function isDoubleNegativeZero(x) {
    return (x===0 && (1/x)===-Infinity);
}
var isFloatNegativeZero = isDoubleNegativeZero;

function strEq(a, b) {
    return a == b;
}

function strOrd(a, b) {
    if(a < b) {
        return 0;
    } else if(a == b) {
        return 1;
    }
    return 2;
}

function jsCatch(act, handler) {
    try {
        return B(A(act,[0]));
    } catch(e) {
        return B(A(handler,[e, 0]));
    }
}

/* Haste represents constructors internally using 1 for the first constructor,
   2 for the second, etc.
   However, dataToTag should use 0, 1, 2, etc. Also, booleans might be unboxed.
 */
function dataToTag(x) {
    if(x instanceof Array) {
        return x[0];
    } else {
        return x;
    }
}

function __word_encodeDouble(d, e) {
    return d * Math.pow(2,e);
}

var __word_encodeFloat = __word_encodeDouble;
var jsRound = Math.round, rintDouble = jsRound, rintFloat = jsRound;
var jsTrunc = Math.trunc ? Math.trunc : function(x) {
    return x < 0 ? Math.ceil(x) : Math.floor(x);
};
function jsRoundW(n) {
    return Math.abs(jsTrunc(n));
}
var realWorld = undefined;
if(typeof _ == 'undefined') {
    var _ = undefined;
}

function popCnt64(i) {
    return popCnt(I_getBits(i,0)) + popCnt(I_getBits(i,1));
}

function popCnt(i) {
    i = i - ((i >> 1) & 0x55555555);
    i = (i & 0x33333333) + ((i >> 2) & 0x33333333);
    return (((i + (i >> 4)) & 0x0F0F0F0F) * 0x01010101) >> 24;
}

// Scratch space for byte arrays.
var rts_scratchBuf = new ArrayBuffer(8);
var rts_scratchW32 = new Uint32Array(rts_scratchBuf);
var rts_scratchFloat = new Float32Array(rts_scratchBuf);
var rts_scratchDouble = new Float64Array(rts_scratchBuf);

function decodeFloat(x) {
    if(x === 0) {
        return [0,1,0,0,0];
    }
    rts_scratchFloat[0] = x;
    var sign = x < 0 ? -1 : 1;
    var exp = ((rts_scratchW32[0] >> 23) & 0xff) - 150;
    var man = rts_scratchW32[0] & 0x7fffff;
    if(exp === 0) {
        ++exp;
    } else {
        man |= (1 << 23);
    }
    return [0, sign*man, exp];
}

function decodeDouble(x) {
    if(x === 0) {
        // GHC 7.10+ *really* doesn't like 0 to be represented as anything
        // but zeroes all the way.
        return [0,1,0,0,0];
    }
    rts_scratchDouble[0] = x;
    var sign = x < 0 ? -1 : 1;
    var manHigh = rts_scratchW32[1] & 0xfffff;
    var manLow = rts_scratchW32[0];
    var exp = ((rts_scratchW32[1] >> 20) & 0x7ff) - 1075;
    if(exp === 0) {
        ++exp;
    } else {
        manHigh |= (1 << 20);
    }
    return [0, sign, manHigh, manLow, exp];
}

function jsAlert(val) {
    if(typeof alert != 'undefined') {
        alert(val);
    } else {
        print(val);
    }
}

function jsLog(val) {
    console.log(val);
}

function jsPrompt(str) {
    var val;
    if(typeof prompt != 'undefined') {
        val = prompt(str);
    } else {
        print(str);
        val = readline();
    }
    return val == undefined ? '' : val.toString();
}

function jsEval(str) {
    var x = eval(str);
    return x == undefined ? '' : x.toString();
}

function isNull(obj) {
    return obj === null;
}

function jsRead(str) {
    return Number(str);
}

function jsShowI(val) {return val.toString();}
function jsShow(val) {
    var ret = val.toString();
    return val == Math.round(val) ? ret + '.0' : ret;
}

window['jsGetMouseCoords'] = function jsGetMouseCoords(e) {
    var posx = 0;
    var posy = 0;
    if (!e) var e = window.event;
    if (e.pageX || e.pageY) 	{
	posx = e.pageX;
	posy = e.pageY;
    }
    else if (e.clientX || e.clientY) 	{
	posx = e.clientX + document.body.scrollLeft
	    + document.documentElement.scrollLeft;
	posy = e.clientY + document.body.scrollTop
	    + document.documentElement.scrollTop;
    }
    return [posx - (e.currentTarget.offsetLeft || 0),
	    posy - (e.currentTarget.offsetTop || 0)];
}

function jsGet(elem, prop) {
    return elem[prop].toString();
}

function jsSet(elem, prop, val) {
    elem[prop] = val;
}

function jsGetAttr(elem, prop) {
    if(elem.hasAttribute(prop)) {
        return elem.getAttribute(prop).toString();
    } else {
        return "";
    }
}

function jsSetAttr(elem, prop, val) {
    elem.setAttribute(prop, val);
}

function jsGetStyle(elem, prop) {
    return elem.style[prop].toString();
}

function jsSetStyle(elem, prop, val) {
    elem.style[prop] = val;
}

function jsKillChild(child, parent) {
    parent.removeChild(child);
}

function jsClearChildren(elem) {
    while(elem.hasChildNodes()){
        elem.removeChild(elem.lastChild);
    }
}

function jsFind(elem) {
    var e = document.getElementById(elem)
    if(e) {
        return [1,e];
    }
    return [0];
}

function jsElemsByClassName(cls) {
    var es = document.getElementsByClassName(cls);
    var els = [0];

    for (var i = es.length-1; i >= 0; --i) {
        els = [1, es[i], els];
    }
    return els;
}

function jsQuerySelectorAll(elem, query) {
    var els = [0], nl;

    if (!elem || typeof elem.querySelectorAll !== 'function') {
        return els;
    }

    nl = elem.querySelectorAll(query);

    for (var i = nl.length-1; i >= 0; --i) {
        els = [1, nl[i], els];
    }

    return els;
}

function jsCreateElem(tag) {
    return document.createElement(tag);
}

function jsCreateTextNode(str) {
    return document.createTextNode(str);
}

function jsGetChildBefore(elem) {
    elem = elem.previousSibling;
    while(elem) {
        if(typeof elem.tagName != 'undefined') {
            return [1,elem];
        }
        elem = elem.previousSibling;
    }
    return [0];
}

function jsGetLastChild(elem) {
    var len = elem.childNodes.length;
    for(var i = len-1; i >= 0; --i) {
        if(typeof elem.childNodes[i].tagName != 'undefined') {
            return [1,elem.childNodes[i]];
        }
    }
    return [0];
}


function jsGetFirstChild(elem) {
    var len = elem.childNodes.length;
    for(var i = 0; i < len; i++) {
        if(typeof elem.childNodes[i].tagName != 'undefined') {
            return [1,elem.childNodes[i]];
        }
    }
    return [0];
}


function jsGetChildren(elem) {
    var children = [0];
    var len = elem.childNodes.length;
    for(var i = len-1; i >= 0; --i) {
        if(typeof elem.childNodes[i].tagName != 'undefined') {
            children = [1, elem.childNodes[i], children];
        }
    }
    return children;
}

function jsSetChildren(elem, children) {
    children = E(children);
    jsClearChildren(elem, 0);
    while(children[0] === 1) {
        elem.appendChild(E(children[1]));
        children = E(children[2]);
    }
}

function jsAppendChild(child, container) {
    container.appendChild(child);
}

function jsAddChildBefore(child, container, after) {
    container.insertBefore(child, after);
}

var jsRand = Math.random;

// Concatenate a Haskell list of JS strings
function jsCat(strs, sep) {
    var arr = [];
    strs = E(strs);
    while(strs[0]) {
        strs = E(strs);
        arr.push(E(strs[1]));
        strs = E(strs[2]);
    }
    return arr.join(sep);
}

// JSON stringify a string
function jsStringify(str) {
    return JSON.stringify(str);
}

// Parse a JSON message into a Haste.JSON.JSON value.
// As this pokes around inside Haskell values, it'll need to be updated if:
// * Haste.JSON.JSON changes;
// * E() starts to choke on non-thunks;
// * data constructor code generation changes; or
// * Just and Nothing change tags.
function jsParseJSON(str) {
    try {
        var js = JSON.parse(str);
        var hs = toHS(js);
    } catch(_) {
        return [0];
    }
    return [1,hs];
}

function toHS(obj) {
    switch(typeof obj) {
    case 'number':
        return [0, jsRead(obj)];
    case 'string':
        return [1, obj];
    case 'boolean':
        return [2, obj]; // Booleans are special wrt constructor tags!
    case 'object':
        if(obj instanceof Array) {
            return [3, arr2lst_json(obj, 0)];
        } else if (obj == null) {
            return [5];
        } else {
            // Object type but not array - it's a dictionary.
            // The RFC doesn't say anything about the ordering of keys, but
            // considering that lots of people rely on keys being "in order" as
            // defined by "the same way someone put them in at the other end,"
            // it's probably a good idea to put some cycles into meeting their
            // misguided expectations.
            var ks = [];
            for(var k in obj) {
                ks.unshift(k);
            }
            var xs = [0];
            for(var i = 0; i < ks.length; i++) {
                xs = [1, [0, ks[i], toHS(obj[ks[i]])], xs];
            }
            return [4, xs];
        }
    }
}

function arr2lst_json(arr, elem) {
    if(elem >= arr.length) {
        return [0];
    }
    return [1, toHS(arr[elem]), new T(function() {return arr2lst_json(arr,elem+1);}),true]
}

function ajaxReq(method, url, async, postdata, cb) {
    var xhr = new XMLHttpRequest();
    xhr.open(method, url, async);

    if(method == "POST") {
        xhr.setRequestHeader("Content-type",
                             "application/x-www-form-urlencoded");
    }
    xhr.onreadystatechange = function() {
        if(xhr.readyState == 4) {
            if(xhr.status == 200) {
                B(A(cb,[[1,xhr.responseText],0]));
            } else {
                B(A(cb,[[0],0])); // Nothing
            }
        }
    }
    xhr.send(postdata);
}

/* gettimeofday(2) */
function gettimeofday(tv, _tz) {
    var t = new Date().getTime();
    writeOffAddr("i32", 4, tv, 0, (t/1000)|0);
    writeOffAddr("i32", 4, tv, 1, ((t%1000)*1000)|0);
    return 0;
}

/* Utility functions for working with JSStrings. */

var _jss_singleton = String.fromCharCode;

function _jss_cons(c,s) {return String.fromCharCode(c)+s;}
function _jss_snoc(s,c) {return s+String.fromCharCode(c);}
function _jss_append(a,b) {return a+b;}
function _jss_len(s) {return s.length;}
function _jss_index(s,i) {return s.charCodeAt(i);}
function _jss_drop(s,i) {return s.substr(i);}
function _jss_substr(s,a,b) {return s.substr(a,b);}
function _jss_take(n,s) {return s.substr(0,n);}
// TODO: incorrect for some unusual characters.
function _jss_rev(s) {return s.split("").reverse().join("");}

function _jss_map(f,s) {
    f = E(f);
    var s2 = '';
    for(var i in s) {
        s2 += String.fromCharCode(E(f(s.charCodeAt(i))));
    }
    return s2;
}

function _jss_foldl(f,x,s) {
    f = E(f);
    for(var i in s) {
        x = A(f,[x,s.charCodeAt(i)]);
    }
    return x;
}

function _jss_re_match(s,re) {return s.search(re)>=0;}
function _jss_re_compile(re,fs) {return new RegExp(re,fs);}
function _jss_re_replace(s,re,rep) {return s.replace(re,rep);}

function _jss_re_find(re,s) {
    var a = s.match(re);
    return a ? mklst(a) : [0];
}

function mklst(arr) {
    var l = [0], len = arr.length-1;
    for(var i = 0; i <= len; ++i) {
        l = [1,arr[len-i],l];
    }
    return l;
}

// Create a little endian ArrayBuffer representation of something.
function toABHost(v, n, x) {
    var a = new ArrayBuffer(n);
    new window[v](a)[0] = x;
    return a;
}

function toABSwap(v, n, x) {
    var a = new ArrayBuffer(n);
    new window[v](a)[0] = x;
    var bs = new Uint8Array(a);
    for(var i = 0, j = n-1; i < j; ++i, --j) {
        var tmp = bs[i];
        bs[i] = bs[j];
        bs[j] = tmp;
    }
    return a;
}

window['toABle'] = toABHost;
window['toABbe'] = toABSwap;

// Swap byte order if host is not little endian.
var buffer = new ArrayBuffer(2);
new DataView(buffer).setInt16(0, 256, true);
if(new Int16Array(buffer)[0] !== 256) {
    window['toABle'] = toABSwap;
    window['toABbe'] = toABHost;
}

// MVar implementation.
// Since Haste isn't concurrent, takeMVar and putMVar don't block on empty
// and full MVars respectively, but terminate the program since they would
// otherwise be blocking forever.

function newMVar() {
    return ({empty: true});
}

function tryTakeMVar(mv) {
    if(mv.empty) {
        return [0, 0, undefined];
    } else {
        var val = mv.x;
        mv.empty = true;
        mv.x = null;
        return [0, 1, val];
    }
}

function takeMVar(mv) {
    if(mv.empty) {
        // TODO: real BlockedOnDeadMVar exception, perhaps?
        err("Attempted to take empty MVar!");
    }
    var val = mv.x;
    mv.empty = true;
    mv.x = null;
    return val;
}

function putMVar(mv, val) {
    if(!mv.empty) {
        // TODO: real BlockedOnDeadMVar exception, perhaps?
        err("Attempted to put full MVar!");
    }
    mv.empty = false;
    mv.x = val;
}

function tryPutMVar(mv, val) {
    if(!mv.empty) {
        return 0;
    } else {
        mv.empty = false;
        mv.x = val;
        return 1;
    }
}

function sameMVar(a, b) {
    return (a == b);
}

function isEmptyMVar(mv) {
    return mv.empty ? 1 : 0;
}

// Implementation of stable names.
// Unlike native GHC, the garbage collector isn't going to move data around
// in a way that we can detect, so each object could serve as its own stable
// name if it weren't for the fact we can't turn a JS reference into an
// integer.
// So instead, each object has a unique integer attached to it, which serves
// as its stable name.

var __next_stable_name = 1;
var __stable_table;

function makeStableName(x) {
    if(x instanceof Object) {
        if(!x.stableName) {
            x.stableName = __next_stable_name;
            __next_stable_name += 1;
        }
        return {type: 'obj', name: x.stableName};
    } else {
        return {type: 'prim', name: Number(x)};
    }
}

function eqStableName(x, y) {
    return (x.type == y.type && x.name == y.name) ? 1 : 0;
}

var Integer = function(bits, sign) {
  this.bits_ = [];
  this.sign_ = sign;

  var top = true;
  for (var i = bits.length - 1; i >= 0; i--) {
    var val = bits[i] | 0;
    if (!top || val != sign) {
      this.bits_[i] = val;
      top = false;
    }
  }
};

Integer.IntCache_ = {};

var I_fromInt = function(value) {
  if (-128 <= value && value < 128) {
    var cachedObj = Integer.IntCache_[value];
    if (cachedObj) {
      return cachedObj;
    }
  }

  var obj = new Integer([value | 0], value < 0 ? -1 : 0);
  if (-128 <= value && value < 128) {
    Integer.IntCache_[value] = obj;
  }
  return obj;
};

var I_fromNumber = function(value) {
  if (isNaN(value) || !isFinite(value)) {
    return Integer.ZERO;
  } else if (value < 0) {
    return I_negate(I_fromNumber(-value));
  } else {
    var bits = [];
    var pow = 1;
    for (var i = 0; value >= pow; i++) {
      bits[i] = (value / pow) | 0;
      pow *= Integer.TWO_PWR_32_DBL_;
    }
    return new Integer(bits, 0);
  }
};

var I_fromBits = function(bits) {
  var high = bits[bits.length - 1];
  return new Integer(bits, high & (1 << 31) ? -1 : 0);
};

var I_fromString = function(str, opt_radix) {
  if (str.length == 0) {
    throw Error('number format error: empty string');
  }

  var radix = opt_radix || 10;
  if (radix < 2 || 36 < radix) {
    throw Error('radix out of range: ' + radix);
  }

  if (str.charAt(0) == '-') {
    return I_negate(I_fromString(str.substring(1), radix));
  } else if (str.indexOf('-') >= 0) {
    throw Error('number format error: interior "-" character');
  }

  var radixToPower = I_fromNumber(Math.pow(radix, 8));

  var result = Integer.ZERO;
  for (var i = 0; i < str.length; i += 8) {
    var size = Math.min(8, str.length - i);
    var value = parseInt(str.substring(i, i + size), radix);
    if (size < 8) {
      var power = I_fromNumber(Math.pow(radix, size));
      result = I_add(I_mul(result, power), I_fromNumber(value));
    } else {
      result = I_mul(result, radixToPower);
      result = I_add(result, I_fromNumber(value));
    }
  }
  return result;
};


Integer.TWO_PWR_32_DBL_ = (1 << 16) * (1 << 16);
Integer.ZERO = I_fromInt(0);
Integer.ONE = I_fromInt(1);
Integer.TWO_PWR_24_ = I_fromInt(1 << 24);

var I_toInt = function(self) {
  return self.bits_.length > 0 ? self.bits_[0] : self.sign_;
};

var I_toWord = function(self) {
  return I_toInt(self) >>> 0;
};

var I_toNumber = function(self) {
  if (isNegative(self)) {
    return -I_toNumber(I_negate(self));
  } else {
    var val = 0;
    var pow = 1;
    for (var i = 0; i < self.bits_.length; i++) {
      val += I_getBitsUnsigned(self, i) * pow;
      pow *= Integer.TWO_PWR_32_DBL_;
    }
    return val;
  }
};

var I_getBits = function(self, index) {
  if (index < 0) {
    return 0;
  } else if (index < self.bits_.length) {
    return self.bits_[index];
  } else {
    return self.sign_;
  }
};

var I_getBitsUnsigned = function(self, index) {
  var val = I_getBits(self, index);
  return val >= 0 ? val : Integer.TWO_PWR_32_DBL_ + val;
};

var getSign = function(self) {
  return self.sign_;
};

var isZero = function(self) {
  if (self.sign_ != 0) {
    return false;
  }
  for (var i = 0; i < self.bits_.length; i++) {
    if (self.bits_[i] != 0) {
      return false;
    }
  }
  return true;
};

var isNegative = function(self) {
  return self.sign_ == -1;
};

var isOdd = function(self) {
  return (self.bits_.length == 0) && (self.sign_ == -1) ||
         (self.bits_.length > 0) && ((self.bits_[0] & 1) != 0);
};

var I_equals = function(self, other) {
  if (self.sign_ != other.sign_) {
    return false;
  }
  var len = Math.max(self.bits_.length, other.bits_.length);
  for (var i = 0; i < len; i++) {
    if (I_getBits(self, i) != I_getBits(other, i)) {
      return false;
    }
  }
  return true;
};

var I_notEquals = function(self, other) {
  return !I_equals(self, other);
};

var I_greaterThan = function(self, other) {
  return I_compare(self, other) > 0;
};

var I_greaterThanOrEqual = function(self, other) {
  return I_compare(self, other) >= 0;
};

var I_lessThan = function(self, other) {
  return I_compare(self, other) < 0;
};

var I_lessThanOrEqual = function(self, other) {
  return I_compare(self, other) <= 0;
};

var I_compare = function(self, other) {
  var diff = I_sub(self, other);
  if (isNegative(diff)) {
    return -1;
  } else if (isZero(diff)) {
    return 0;
  } else {
    return +1;
  }
};

var I_compareInt = function(self, other) {
  return I_compare(self, I_fromInt(other));
}

var shorten = function(self, numBits) {
  var arr_index = (numBits - 1) >> 5;
  var bit_index = (numBits - 1) % 32;
  var bits = [];
  for (var i = 0; i < arr_index; i++) {
    bits[i] = I_getBits(self, i);
  }
  var sigBits = bit_index == 31 ? 0xFFFFFFFF : (1 << (bit_index + 1)) - 1;
  var val = I_getBits(self, arr_index) & sigBits;
  if (val & (1 << bit_index)) {
    val |= 0xFFFFFFFF - sigBits;
    bits[arr_index] = val;
    return new Integer(bits, -1);
  } else {
    bits[arr_index] = val;
    return new Integer(bits, 0);
  }
};

var I_negate = function(self) {
  return I_add(not(self), Integer.ONE);
};

var I_add = function(self, other) {
  var len = Math.max(self.bits_.length, other.bits_.length);
  var arr = [];
  var carry = 0;

  for (var i = 0; i <= len; i++) {
    var a1 = I_getBits(self, i) >>> 16;
    var a0 = I_getBits(self, i) & 0xFFFF;

    var b1 = I_getBits(other, i) >>> 16;
    var b0 = I_getBits(other, i) & 0xFFFF;

    var c0 = carry + a0 + b0;
    var c1 = (c0 >>> 16) + a1 + b1;
    carry = c1 >>> 16;
    c0 &= 0xFFFF;
    c1 &= 0xFFFF;
    arr[i] = (c1 << 16) | c0;
  }
  return I_fromBits(arr);
};

var I_sub = function(self, other) {
  return I_add(self, I_negate(other));
};

var I_mul = function(self, other) {
  if (isZero(self)) {
    return Integer.ZERO;
  } else if (isZero(other)) {
    return Integer.ZERO;
  }

  if (isNegative(self)) {
    if (isNegative(other)) {
      return I_mul(I_negate(self), I_negate(other));
    } else {
      return I_negate(I_mul(I_negate(self), other));
    }
  } else if (isNegative(other)) {
    return I_negate(I_mul(self, I_negate(other)));
  }

  if (I_lessThan(self, Integer.TWO_PWR_24_) &&
      I_lessThan(other, Integer.TWO_PWR_24_)) {
    return I_fromNumber(I_toNumber(self) * I_toNumber(other));
  }

  var len = self.bits_.length + other.bits_.length;
  var arr = [];
  for (var i = 0; i < 2 * len; i++) {
    arr[i] = 0;
  }
  for (var i = 0; i < self.bits_.length; i++) {
    for (var j = 0; j < other.bits_.length; j++) {
      var a1 = I_getBits(self, i) >>> 16;
      var a0 = I_getBits(self, i) & 0xFFFF;

      var b1 = I_getBits(other, j) >>> 16;
      var b0 = I_getBits(other, j) & 0xFFFF;

      arr[2 * i + 2 * j] += a0 * b0;
      Integer.carry16_(arr, 2 * i + 2 * j);
      arr[2 * i + 2 * j + 1] += a1 * b0;
      Integer.carry16_(arr, 2 * i + 2 * j + 1);
      arr[2 * i + 2 * j + 1] += a0 * b1;
      Integer.carry16_(arr, 2 * i + 2 * j + 1);
      arr[2 * i + 2 * j + 2] += a1 * b1;
      Integer.carry16_(arr, 2 * i + 2 * j + 2);
    }
  }

  for (var i = 0; i < len; i++) {
    arr[i] = (arr[2 * i + 1] << 16) | arr[2 * i];
  }
  for (var i = len; i < 2 * len; i++) {
    arr[i] = 0;
  }
  return new Integer(arr, 0);
};

Integer.carry16_ = function(bits, index) {
  while ((bits[index] & 0xFFFF) != bits[index]) {
    bits[index + 1] += bits[index] >>> 16;
    bits[index] &= 0xFFFF;
  }
};

var I_mod = function(self, other) {
  return I_rem(I_add(other, I_rem(self, other)), other);
}

var I_div = function(self, other) {
  if(I_greaterThan(self, Integer.ZERO) != I_greaterThan(other, Integer.ZERO)) {
    if(I_rem(self, other) != Integer.ZERO) {
      return I_sub(I_quot(self, other), Integer.ONE);
    }
  }
  return I_quot(self, other);
}

var I_quotRem = function(self, other) {
  return [0, I_quot(self, other), I_rem(self, other)];
}

var I_divMod = function(self, other) {
  return [0, I_div(self, other), I_mod(self, other)];
}

var I_quot = function(self, other) {
  if (isZero(other)) {
    throw Error('division by zero');
  } else if (isZero(self)) {
    return Integer.ZERO;
  }

  if (isNegative(self)) {
    if (isNegative(other)) {
      return I_quot(I_negate(self), I_negate(other));
    } else {
      return I_negate(I_quot(I_negate(self), other));
    }
  } else if (isNegative(other)) {
    return I_negate(I_quot(self, I_negate(other)));
  }

  var res = Integer.ZERO;
  var rem = self;
  while (I_greaterThanOrEqual(rem, other)) {
    var approx = Math.max(1, Math.floor(I_toNumber(rem) / I_toNumber(other)));
    var log2 = Math.ceil(Math.log(approx) / Math.LN2);
    var delta = (log2 <= 48) ? 1 : Math.pow(2, log2 - 48);
    var approxRes = I_fromNumber(approx);
    var approxRem = I_mul(approxRes, other);
    while (isNegative(approxRem) || I_greaterThan(approxRem, rem)) {
      approx -= delta;
      approxRes = I_fromNumber(approx);
      approxRem = I_mul(approxRes, other);
    }

    if (isZero(approxRes)) {
      approxRes = Integer.ONE;
    }

    res = I_add(res, approxRes);
    rem = I_sub(rem, approxRem);
  }
  return res;
};

var I_rem = function(self, other) {
  return I_sub(self, I_mul(I_quot(self, other), other));
};

var not = function(self) {
  var len = self.bits_.length;
  var arr = [];
  for (var i = 0; i < len; i++) {
    arr[i] = ~self.bits_[i];
  }
  return new Integer(arr, ~self.sign_);
};

var I_and = function(self, other) {
  var len = Math.max(self.bits_.length, other.bits_.length);
  var arr = [];
  for (var i = 0; i < len; i++) {
    arr[i] = I_getBits(self, i) & I_getBits(other, i);
  }
  return new Integer(arr, self.sign_ & other.sign_);
};

var I_or = function(self, other) {
  var len = Math.max(self.bits_.length, other.bits_.length);
  var arr = [];
  for (var i = 0; i < len; i++) {
    arr[i] = I_getBits(self, i) | I_getBits(other, i);
  }
  return new Integer(arr, self.sign_ | other.sign_);
};

var I_xor = function(self, other) {
  var len = Math.max(self.bits_.length, other.bits_.length);
  var arr = [];
  for (var i = 0; i < len; i++) {
    arr[i] = I_getBits(self, i) ^ I_getBits(other, i);
  }
  return new Integer(arr, self.sign_ ^ other.sign_);
};

var I_shiftLeft = function(self, numBits) {
  var arr_delta = numBits >> 5;
  var bit_delta = numBits % 32;
  var len = self.bits_.length + arr_delta + (bit_delta > 0 ? 1 : 0);
  var arr = [];
  for (var i = 0; i < len; i++) {
    if (bit_delta > 0) {
      arr[i] = (I_getBits(self, i - arr_delta) << bit_delta) |
               (I_getBits(self, i - arr_delta - 1) >>> (32 - bit_delta));
    } else {
      arr[i] = I_getBits(self, i - arr_delta);
    }
  }
  return new Integer(arr, self.sign_);
};

var I_shiftRight = function(self, numBits) {
  var arr_delta = numBits >> 5;
  var bit_delta = numBits % 32;
  var len = self.bits_.length - arr_delta;
  var arr = [];
  for (var i = 0; i < len; i++) {
    if (bit_delta > 0) {
      arr[i] = (I_getBits(self, i + arr_delta) >>> bit_delta) |
               (I_getBits(self, i + arr_delta + 1) << (32 - bit_delta));
    } else {
      arr[i] = I_getBits(self, i + arr_delta);
    }
  }
  return new Integer(arr, self.sign_);
};

var I_signum = function(self) {
  var cmp = I_compare(self, Integer.ZERO);
  if(cmp > 0) {
    return Integer.ONE
  }
  if(cmp < 0) {
    return I_sub(Integer.ZERO, Integer.ONE);
  }
  return Integer.ZERO;
};

var I_abs = function(self) {
  if(I_compare(self, Integer.ZERO) < 0) {
    return I_sub(Integer.ZERO, self);
  }
  return self;
};

var I_decodeDouble = function(x) {
  var dec = decodeDouble(x);
  var mantissa = I_fromBits([dec[3], dec[2]]);
  if(dec[1] < 0) {
    mantissa = I_negate(mantissa);
  }
  return [0, dec[4], mantissa];
}

var I_toString = function(self) {
  var radix = 10;

  if (isZero(self)) {
    return '0';
  } else if (isNegative(self)) {
    return '-' + I_toString(I_negate(self));
  }

  var radixToPower = I_fromNumber(Math.pow(radix, 6));

  var rem = self;
  var result = '';
  while (true) {
    var remDiv = I_div(rem, radixToPower);
    var intval = I_toInt(I_sub(rem, I_mul(remDiv, radixToPower)));
    var digits = intval.toString();

    rem = remDiv;
    if (isZero(rem)) {
      return digits + result;
    } else {
      while (digits.length < 6) {
        digits = '0' + digits;
      }
      result = '' + digits + result;
    }
  }
};

var I_fromRat = function(a, b) {
    return I_toNumber(a) / I_toNumber(b);
}

function I_fromInt64(x) {
    return I_fromBits([x.getLowBits(), x.getHighBits()]);
}

function I_toInt64(x) {
    return Long.fromBits(I_getBits(x, 0), I_getBits(x, 1));
}

function I_fromWord64(x) {
    return x;
}

function I_toWord64(x) {
    return I_rem(I_add(__w64_max, x), __w64_max);
}

// Copyright 2009 The Closure Library Authors. All Rights Reserved.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS-IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

var Long = function(low, high) {
  this.low_ = low | 0;
  this.high_ = high | 0;
};

Long.IntCache_ = {};

Long.fromInt = function(value) {
  if (-128 <= value && value < 128) {
    var cachedObj = Long.IntCache_[value];
    if (cachedObj) {
      return cachedObj;
    }
  }

  var obj = new Long(value | 0, value < 0 ? -1 : 0);
  if (-128 <= value && value < 128) {
    Long.IntCache_[value] = obj;
  }
  return obj;
};

Long.fromNumber = function(value) {
  if (isNaN(value) || !isFinite(value)) {
    return Long.ZERO;
  } else if (value <= -Long.TWO_PWR_63_DBL_) {
    return Long.MIN_VALUE;
  } else if (value + 1 >= Long.TWO_PWR_63_DBL_) {
    return Long.MAX_VALUE;
  } else if (value < 0) {
    return Long.fromNumber(-value).negate();
  } else {
    return new Long(
        (value % Long.TWO_PWR_32_DBL_) | 0,
        (value / Long.TWO_PWR_32_DBL_) | 0);
  }
};

Long.fromBits = function(lowBits, highBits) {
  return new Long(lowBits, highBits);
};

Long.TWO_PWR_16_DBL_ = 1 << 16;
Long.TWO_PWR_24_DBL_ = 1 << 24;
Long.TWO_PWR_32_DBL_ =
    Long.TWO_PWR_16_DBL_ * Long.TWO_PWR_16_DBL_;
Long.TWO_PWR_31_DBL_ =
    Long.TWO_PWR_32_DBL_ / 2;
Long.TWO_PWR_48_DBL_ =
    Long.TWO_PWR_32_DBL_ * Long.TWO_PWR_16_DBL_;
Long.TWO_PWR_64_DBL_ =
    Long.TWO_PWR_32_DBL_ * Long.TWO_PWR_32_DBL_;
Long.TWO_PWR_63_DBL_ =
    Long.TWO_PWR_64_DBL_ / 2;
Long.ZERO = Long.fromInt(0);
Long.ONE = Long.fromInt(1);
Long.NEG_ONE = Long.fromInt(-1);
Long.MAX_VALUE =
    Long.fromBits(0xFFFFFFFF | 0, 0x7FFFFFFF | 0);
Long.MIN_VALUE = Long.fromBits(0, 0x80000000 | 0);
Long.TWO_PWR_24_ = Long.fromInt(1 << 24);

Long.prototype.toInt = function() {
  return this.low_;
};

Long.prototype.toNumber = function() {
  return this.high_ * Long.TWO_PWR_32_DBL_ +
         this.getLowBitsUnsigned();
};

Long.prototype.getHighBits = function() {
  return this.high_;
};

Long.prototype.getLowBits = function() {
  return this.low_;
};

Long.prototype.getLowBitsUnsigned = function() {
  return (this.low_ >= 0) ?
      this.low_ : Long.TWO_PWR_32_DBL_ + this.low_;
};

Long.prototype.isZero = function() {
  return this.high_ == 0 && this.low_ == 0;
};

Long.prototype.isNegative = function() {
  return this.high_ < 0;
};

Long.prototype.isOdd = function() {
  return (this.low_ & 1) == 1;
};

Long.prototype.equals = function(other) {
  return (this.high_ == other.high_) && (this.low_ == other.low_);
};

Long.prototype.notEquals = function(other) {
  return (this.high_ != other.high_) || (this.low_ != other.low_);
};

Long.prototype.lessThan = function(other) {
  return this.compare(other) < 0;
};

Long.prototype.lessThanOrEqual = function(other) {
  return this.compare(other) <= 0;
};

Long.prototype.greaterThan = function(other) {
  return this.compare(other) > 0;
};

Long.prototype.greaterThanOrEqual = function(other) {
  return this.compare(other) >= 0;
};

Long.prototype.compare = function(other) {
  if (this.equals(other)) {
    return 0;
  }

  var thisNeg = this.isNegative();
  var otherNeg = other.isNegative();
  if (thisNeg && !otherNeg) {
    return -1;
  }
  if (!thisNeg && otherNeg) {
    return 1;
  }

  if (this.subtract(other).isNegative()) {
    return -1;
  } else {
    return 1;
  }
};

Long.prototype.negate = function() {
  if (this.equals(Long.MIN_VALUE)) {
    return Long.MIN_VALUE;
  } else {
    return this.not().add(Long.ONE);
  }
};

Long.prototype.add = function(other) {
  var a48 = this.high_ >>> 16;
  var a32 = this.high_ & 0xFFFF;
  var a16 = this.low_ >>> 16;
  var a00 = this.low_ & 0xFFFF;

  var b48 = other.high_ >>> 16;
  var b32 = other.high_ & 0xFFFF;
  var b16 = other.low_ >>> 16;
  var b00 = other.low_ & 0xFFFF;

  var c48 = 0, c32 = 0, c16 = 0, c00 = 0;
  c00 += a00 + b00;
  c16 += c00 >>> 16;
  c00 &= 0xFFFF;
  c16 += a16 + b16;
  c32 += c16 >>> 16;
  c16 &= 0xFFFF;
  c32 += a32 + b32;
  c48 += c32 >>> 16;
  c32 &= 0xFFFF;
  c48 += a48 + b48;
  c48 &= 0xFFFF;
  return Long.fromBits((c16 << 16) | c00, (c48 << 16) | c32);
};

Long.prototype.subtract = function(other) {
  return this.add(other.negate());
};

Long.prototype.multiply = function(other) {
  if (this.isZero()) {
    return Long.ZERO;
  } else if (other.isZero()) {
    return Long.ZERO;
  }

  if (this.equals(Long.MIN_VALUE)) {
    return other.isOdd() ? Long.MIN_VALUE : Long.ZERO;
  } else if (other.equals(Long.MIN_VALUE)) {
    return this.isOdd() ? Long.MIN_VALUE : Long.ZERO;
  }

  if (this.isNegative()) {
    if (other.isNegative()) {
      return this.negate().multiply(other.negate());
    } else {
      return this.negate().multiply(other).negate();
    }
  } else if (other.isNegative()) {
    return this.multiply(other.negate()).negate();
  }

  if (this.lessThan(Long.TWO_PWR_24_) &&
      other.lessThan(Long.TWO_PWR_24_)) {
    return Long.fromNumber(this.toNumber() * other.toNumber());
  }

  var a48 = this.high_ >>> 16;
  var a32 = this.high_ & 0xFFFF;
  var a16 = this.low_ >>> 16;
  var a00 = this.low_ & 0xFFFF;

  var b48 = other.high_ >>> 16;
  var b32 = other.high_ & 0xFFFF;
  var b16 = other.low_ >>> 16;
  var b00 = other.low_ & 0xFFFF;

  var c48 = 0, c32 = 0, c16 = 0, c00 = 0;
  c00 += a00 * b00;
  c16 += c00 >>> 16;
  c00 &= 0xFFFF;
  c16 += a16 * b00;
  c32 += c16 >>> 16;
  c16 &= 0xFFFF;
  c16 += a00 * b16;
  c32 += c16 >>> 16;
  c16 &= 0xFFFF;
  c32 += a32 * b00;
  c48 += c32 >>> 16;
  c32 &= 0xFFFF;
  c32 += a16 * b16;
  c48 += c32 >>> 16;
  c32 &= 0xFFFF;
  c32 += a00 * b32;
  c48 += c32 >>> 16;
  c32 &= 0xFFFF;
  c48 += a48 * b00 + a32 * b16 + a16 * b32 + a00 * b48;
  c48 &= 0xFFFF;
  return Long.fromBits((c16 << 16) | c00, (c48 << 16) | c32);
};

Long.prototype.div = function(other) {
  if (other.isZero()) {
    throw Error('division by zero');
  } else if (this.isZero()) {
    return Long.ZERO;
  }

  if (this.equals(Long.MIN_VALUE)) {
    if (other.equals(Long.ONE) ||
        other.equals(Long.NEG_ONE)) {
      return Long.MIN_VALUE;
    } else if (other.equals(Long.MIN_VALUE)) {
      return Long.ONE;
    } else {
      var halfThis = this.shiftRight(1);
      var approx = halfThis.div(other).shiftLeft(1);
      if (approx.equals(Long.ZERO)) {
        return other.isNegative() ? Long.ONE : Long.NEG_ONE;
      } else {
        var rem = this.subtract(other.multiply(approx));
        var result = approx.add(rem.div(other));
        return result;
      }
    }
  } else if (other.equals(Long.MIN_VALUE)) {
    return Long.ZERO;
  }

  if (this.isNegative()) {
    if (other.isNegative()) {
      return this.negate().div(other.negate());
    } else {
      return this.negate().div(other).negate();
    }
  } else if (other.isNegative()) {
    return this.div(other.negate()).negate();
  }

  var res = Long.ZERO;
  var rem = this;
  while (rem.greaterThanOrEqual(other)) {
    var approx = Math.max(1, Math.floor(rem.toNumber() / other.toNumber()));

    var log2 = Math.ceil(Math.log(approx) / Math.LN2);
    var delta = (log2 <= 48) ? 1 : Math.pow(2, log2 - 48);

    var approxRes = Long.fromNumber(approx);
    var approxRem = approxRes.multiply(other);
    while (approxRem.isNegative() || approxRem.greaterThan(rem)) {
      approx -= delta;
      approxRes = Long.fromNumber(approx);
      approxRem = approxRes.multiply(other);
    }

    if (approxRes.isZero()) {
      approxRes = Long.ONE;
    }

    res = res.add(approxRes);
    rem = rem.subtract(approxRem);
  }
  return res;
};

Long.prototype.modulo = function(other) {
  return this.subtract(this.div(other).multiply(other));
};

Long.prototype.not = function() {
  return Long.fromBits(~this.low_, ~this.high_);
};

Long.prototype.and = function(other) {
  return Long.fromBits(this.low_ & other.low_,
                                 this.high_ & other.high_);
};

Long.prototype.or = function(other) {
  return Long.fromBits(this.low_ | other.low_,
                                 this.high_ | other.high_);
};

Long.prototype.xor = function(other) {
  return Long.fromBits(this.low_ ^ other.low_,
                                 this.high_ ^ other.high_);
};

Long.prototype.shiftLeft = function(numBits) {
  numBits &= 63;
  if (numBits == 0) {
    return this;
  } else {
    var low = this.low_;
    if (numBits < 32) {
      var high = this.high_;
      return Long.fromBits(
          low << numBits,
          (high << numBits) | (low >>> (32 - numBits)));
    } else {
      return Long.fromBits(0, low << (numBits - 32));
    }
  }
};

Long.prototype.shiftRight = function(numBits) {
  numBits &= 63;
  if (numBits == 0) {
    return this;
  } else {
    var high = this.high_;
    if (numBits < 32) {
      var low = this.low_;
      return Long.fromBits(
          (low >>> numBits) | (high << (32 - numBits)),
          high >> numBits);
    } else {
      return Long.fromBits(
          high >> (numBits - 32),
          high >= 0 ? 0 : -1);
    }
  }
};

Long.prototype.shiftRightUnsigned = function(numBits) {
  numBits &= 63;
  if (numBits == 0) {
    return this;
  } else {
    var high = this.high_;
    if (numBits < 32) {
      var low = this.low_;
      return Long.fromBits(
          (low >>> numBits) | (high << (32 - numBits)),
          high >>> numBits);
    } else if (numBits == 32) {
      return Long.fromBits(high, 0);
    } else {
      return Long.fromBits(high >>> (numBits - 32), 0);
    }
  }
};



// Int64
function hs_eqInt64(x, y) {return x.equals(y);}
function hs_neInt64(x, y) {return !x.equals(y);}
function hs_ltInt64(x, y) {return x.compare(y) < 0;}
function hs_leInt64(x, y) {return x.compare(y) <= 0;}
function hs_gtInt64(x, y) {return x.compare(y) > 0;}
function hs_geInt64(x, y) {return x.compare(y) >= 0;}
function hs_quotInt64(x, y) {return x.div(y);}
function hs_remInt64(x, y) {return x.modulo(y);}
function hs_plusInt64(x, y) {return x.add(y);}
function hs_minusInt64(x, y) {return x.subtract(y);}
function hs_timesInt64(x, y) {return x.multiply(y);}
function hs_negateInt64(x) {return x.negate();}
function hs_uncheckedIShiftL64(x, bits) {return x.shiftLeft(bits);}
function hs_uncheckedIShiftRA64(x, bits) {return x.shiftRight(bits);}
function hs_uncheckedIShiftRL64(x, bits) {return x.shiftRightUnsigned(bits);}
function hs_intToInt64(x) {return new Long(x, 0);}
function hs_int64ToInt(x) {return x.toInt();}



// Word64
function hs_wordToWord64(x) {
    return I_fromInt(x);
}
function hs_word64ToWord(x) {
    return I_toInt(x);
}
function hs_mkWord64(low, high) {
    return I_fromBits([low, high]);
}

var hs_and64 = I_and;
var hs_or64 = I_or;
var hs_xor64 = I_xor;
var __i64_all_ones = I_fromBits([0xffffffff, 0xffffffff]);
function hs_not64(x) {
    return I_xor(x, __i64_all_ones);
}
var hs_eqWord64 = I_equals;
var hs_neWord64 = I_notEquals;
var hs_ltWord64 = I_lessThan;
var hs_leWord64 = I_lessThanOrEqual;
var hs_gtWord64 = I_greaterThan;
var hs_geWord64 = I_greaterThanOrEqual;
var hs_quotWord64 = I_quot;
var hs_remWord64 = I_rem;
var __w64_max = I_fromBits([0,0,1]);
function hs_uncheckedShiftL64(x, bits) {
    return I_rem(I_shiftLeft(x, bits), __w64_max);
}
var hs_uncheckedShiftRL64 = I_shiftRight;
function hs_int64ToWord64(x) {
    var tmp = I_add(__w64_max, I_fromBits([x.getLowBits(), x.getHighBits()]));
    return I_rem(tmp, __w64_max);
}
function hs_word64ToInt64(x) {
    return Long.fromBits(I_getBits(x, 0), I_getBits(x, 1));
}

// Joseph Myers' MD5 implementation, ported to work on typed arrays.
// Used under the BSD license.
function md5cycle(x, k) {
    var a = x[0], b = x[1], c = x[2], d = x[3];

    a = ff(a, b, c, d, k[0], 7, -680876936);
    d = ff(d, a, b, c, k[1], 12, -389564586);
    c = ff(c, d, a, b, k[2], 17,  606105819);
    b = ff(b, c, d, a, k[3], 22, -1044525330);
    a = ff(a, b, c, d, k[4], 7, -176418897);
    d = ff(d, a, b, c, k[5], 12,  1200080426);
    c = ff(c, d, a, b, k[6], 17, -1473231341);
    b = ff(b, c, d, a, k[7], 22, -45705983);
    a = ff(a, b, c, d, k[8], 7,  1770035416);
    d = ff(d, a, b, c, k[9], 12, -1958414417);
    c = ff(c, d, a, b, k[10], 17, -42063);
    b = ff(b, c, d, a, k[11], 22, -1990404162);
    a = ff(a, b, c, d, k[12], 7,  1804603682);
    d = ff(d, a, b, c, k[13], 12, -40341101);
    c = ff(c, d, a, b, k[14], 17, -1502002290);
    b = ff(b, c, d, a, k[15], 22,  1236535329);

    a = gg(a, b, c, d, k[1], 5, -165796510);
    d = gg(d, a, b, c, k[6], 9, -1069501632);
    c = gg(c, d, a, b, k[11], 14,  643717713);
    b = gg(b, c, d, a, k[0], 20, -373897302);
    a = gg(a, b, c, d, k[5], 5, -701558691);
    d = gg(d, a, b, c, k[10], 9,  38016083);
    c = gg(c, d, a, b, k[15], 14, -660478335);
    b = gg(b, c, d, a, k[4], 20, -405537848);
    a = gg(a, b, c, d, k[9], 5,  568446438);
    d = gg(d, a, b, c, k[14], 9, -1019803690);
    c = gg(c, d, a, b, k[3], 14, -187363961);
    b = gg(b, c, d, a, k[8], 20,  1163531501);
    a = gg(a, b, c, d, k[13], 5, -1444681467);
    d = gg(d, a, b, c, k[2], 9, -51403784);
    c = gg(c, d, a, b, k[7], 14,  1735328473);
    b = gg(b, c, d, a, k[12], 20, -1926607734);

    a = hh(a, b, c, d, k[5], 4, -378558);
    d = hh(d, a, b, c, k[8], 11, -2022574463);
    c = hh(c, d, a, b, k[11], 16,  1839030562);
    b = hh(b, c, d, a, k[14], 23, -35309556);
    a = hh(a, b, c, d, k[1], 4, -1530992060);
    d = hh(d, a, b, c, k[4], 11,  1272893353);
    c = hh(c, d, a, b, k[7], 16, -155497632);
    b = hh(b, c, d, a, k[10], 23, -1094730640);
    a = hh(a, b, c, d, k[13], 4,  681279174);
    d = hh(d, a, b, c, k[0], 11, -358537222);
    c = hh(c, d, a, b, k[3], 16, -722521979);
    b = hh(b, c, d, a, k[6], 23,  76029189);
    a = hh(a, b, c, d, k[9], 4, -640364487);
    d = hh(d, a, b, c, k[12], 11, -421815835);
    c = hh(c, d, a, b, k[15], 16,  530742520);
    b = hh(b, c, d, a, k[2], 23, -995338651);

    a = ii(a, b, c, d, k[0], 6, -198630844);
    d = ii(d, a, b, c, k[7], 10,  1126891415);
    c = ii(c, d, a, b, k[14], 15, -1416354905);
    b = ii(b, c, d, a, k[5], 21, -57434055);
    a = ii(a, b, c, d, k[12], 6,  1700485571);
    d = ii(d, a, b, c, k[3], 10, -1894986606);
    c = ii(c, d, a, b, k[10], 15, -1051523);
    b = ii(b, c, d, a, k[1], 21, -2054922799);
    a = ii(a, b, c, d, k[8], 6,  1873313359);
    d = ii(d, a, b, c, k[15], 10, -30611744);
    c = ii(c, d, a, b, k[6], 15, -1560198380);
    b = ii(b, c, d, a, k[13], 21,  1309151649);
    a = ii(a, b, c, d, k[4], 6, -145523070);
    d = ii(d, a, b, c, k[11], 10, -1120210379);
    c = ii(c, d, a, b, k[2], 15,  718787259);
    b = ii(b, c, d, a, k[9], 21, -343485551);

    x[0] = add32(a, x[0]);
    x[1] = add32(b, x[1]);
    x[2] = add32(c, x[2]);
    x[3] = add32(d, x[3]);

}

function cmn(q, a, b, x, s, t) {
    a = add32(add32(a, q), add32(x, t));
    return add32((a << s) | (a >>> (32 - s)), b);
}

function ff(a, b, c, d, x, s, t) {
    return cmn((b & c) | ((~b) & d), a, b, x, s, t);
}

function gg(a, b, c, d, x, s, t) {
    return cmn((b & d) | (c & (~d)), a, b, x, s, t);
}

function hh(a, b, c, d, x, s, t) {
    return cmn(b ^ c ^ d, a, b, x, s, t);
}

function ii(a, b, c, d, x, s, t) {
    return cmn(c ^ (b | (~d)), a, b, x, s, t);
}

function md51(s, n) {
    var a = s['v']['w8'];
    var orig_n = n,
        state = [1732584193, -271733879, -1732584194, 271733878], i;
    for (i=64; i<=n; i+=64) {
        md5cycle(state, md5blk(a.subarray(i-64, i)));
    }
    a = a.subarray(i-64);
    n = n < (i-64) ? 0 : n-(i-64);
    var tail = [0,0,0,0, 0,0,0,0, 0,0,0,0, 0,0,0,0];
    for (i=0; i<n; i++)
        tail[i>>2] |= a[i] << ((i%4) << 3);
    tail[i>>2] |= 0x80 << ((i%4) << 3);
    if (i > 55) {
        md5cycle(state, tail);
        for (i=0; i<16; i++) tail[i] = 0;
    }
    tail[14] = orig_n*8;
    md5cycle(state, tail);
    return state;
}
window['md51'] = md51;

function md5blk(s) {
    var md5blks = [], i;
    for (i=0; i<64; i+=4) {
        md5blks[i>>2] = s[i]
            + (s[i+1] << 8)
            + (s[i+2] << 16)
            + (s[i+3] << 24);
    }
    return md5blks;
}

var hex_chr = '0123456789abcdef'.split('');

function rhex(n)
{
    var s='', j=0;
    for(; j<4; j++)
        s += hex_chr[(n >> (j * 8 + 4)) & 0x0F]
        + hex_chr[(n >> (j * 8)) & 0x0F];
    return s;
}

function hex(x) {
    for (var i=0; i<x.length; i++)
        x[i] = rhex(x[i]);
    return x.join('');
}

function md5(s, n) {
    return hex(md51(s, n));
}

window['md5'] = md5;

function add32(a, b) {
    return (a + b) & 0xFFFFFFFF;
}

function __hsbase_MD5Init(ctx) {}
// Note that this is a one time "update", since that's all that's used by
// GHC.Fingerprint.
function __hsbase_MD5Update(ctx, s, n) {
    ctx.md5 = md51(s, n);
}
function __hsbase_MD5Final(out, ctx) {
    var a = out['v']['i32'];
    a[0] = ctx.md5[0];
    a[1] = ctx.md5[1];
    a[2] = ctx.md5[2];
    a[3] = ctx.md5[3];
}

// Functions for dealing with arrays.

function newArr(n, x) {
    var arr = new Array(n);
    for(var i = 0; i < n; ++i) {
        arr[i] = x;
    }
    return arr;
}

// Create all views at once; perhaps it's wasteful, but it's better than having
// to check for the right view at each read or write.
function newByteArr(n) {
    // Pad the thing to multiples of 8.
    var padding = 8 - n % 8;
    if(padding < 8) {
        n += padding;
    }
    var arr = {};
    var buffer = new ArrayBuffer(n);
    var views = {};
    views['i8']  = new Int8Array(buffer);
    views['i16'] = new Int16Array(buffer);
    views['i32'] = new Int32Array(buffer);
    views['w8']  = new Uint8Array(buffer);
    views['w16'] = new Uint16Array(buffer);
    views['w32'] = new Uint32Array(buffer);
    views['f32'] = new Float32Array(buffer);
    views['f64'] = new Float64Array(buffer);
    arr['b'] = buffer;
    arr['v'] = views;
    // ByteArray and Addr are the same thing, so keep an offset if we get
    // casted.
    arr['off'] = 0;
    return arr;
}
window['newByteArr'] = newByteArr;

// An attempt at emulating pointers enough for ByteString and Text to be
// usable without patching the hell out of them.
// The general idea is that Addr# is a byte array with an associated offset.

function plusAddr(addr, off) {
    var newaddr = {};
    newaddr['off'] = addr['off'] + off;
    newaddr['b']   = addr['b'];
    newaddr['v']   = addr['v'];
    return newaddr;
}

function writeOffAddr(type, elemsize, addr, off, x) {
    addr['v'][type][addr.off/elemsize + off] = x;
}

function readOffAddr(type, elemsize, addr, off) {
    return addr['v'][type][addr.off/elemsize + off];
}

// Two addresses are equal if they point to the same buffer and have the same
// offset. For other comparisons, just use the offsets - nobody in their right
// mind would check if one pointer is less than another, completely unrelated,
// pointer and then act on that information anyway.
function addrEq(a, b) {
    if(a == b) {
        return true;
    }
    return a && b && a['b'] == b['b'] && a['off'] == b['off'];
}

function addrLT(a, b) {
    if(a) {
        return b && a['off'] < b['off'];
    } else {
        return (b != 0); 
    }
}

function addrGT(a, b) {
    if(b) {
        return a && a['off'] > b['off'];
    } else {
        return (a != 0);
    }
}

function withChar(f, charCode) {
    return f(String.fromCharCode(charCode)).charCodeAt(0);
}

function u_towlower(charCode) {
    return withChar(function(c) {return c.toLowerCase()}, charCode);
}

function u_towupper(charCode) {
    return withChar(function(c) {return c.toUpperCase()}, charCode);
}

var u_towtitle = u_towupper;

function u_iswupper(charCode) {
    var c = String.fromCharCode(charCode);
    return c == c.toUpperCase() && c != c.toLowerCase();
}

function u_iswlower(charCode) {
    var c = String.fromCharCode(charCode);
    return  c == c.toLowerCase() && c != c.toUpperCase();
}

function u_iswdigit(charCode) {
    return charCode >= 48 && charCode <= 57;
}

function u_iswcntrl(charCode) {
    return charCode <= 0x1f || charCode == 0x7f;
}

function u_iswspace(charCode) {
    var c = String.fromCharCode(charCode);
    return c.replace(/\s/g,'') != c;
}

function u_iswalpha(charCode) {
    var c = String.fromCharCode(charCode);
    return c.replace(__hs_alphare, '') != c;
}

function u_iswalnum(charCode) {
    return u_iswdigit(charCode) || u_iswalpha(charCode);
}

function u_iswprint(charCode) {
    return !u_iswcntrl(charCode);
}

function u_gencat(c) {
    throw 'u_gencat is only supported with --full-unicode.';
}

// Regex that matches any alphabetic character in any language. Horrible thing.
var __hs_alphare = /[\u0041-\u005A\u0061-\u007A\u00AA\u00B5\u00BA\u00C0-\u00D6\u00D8-\u00F6\u00F8-\u02C1\u02C6-\u02D1\u02E0-\u02E4\u02EC\u02EE\u0370-\u0374\u0376\u0377\u037A-\u037D\u0386\u0388-\u038A\u038C\u038E-\u03A1\u03A3-\u03F5\u03F7-\u0481\u048A-\u0527\u0531-\u0556\u0559\u0561-\u0587\u05D0-\u05EA\u05F0-\u05F2\u0620-\u064A\u066E\u066F\u0671-\u06D3\u06D5\u06E5\u06E6\u06EE\u06EF\u06FA-\u06FC\u06FF\u0710\u0712-\u072F\u074D-\u07A5\u07B1\u07CA-\u07EA\u07F4\u07F5\u07FA\u0800-\u0815\u081A\u0824\u0828\u0840-\u0858\u08A0\u08A2-\u08AC\u0904-\u0939\u093D\u0950\u0958-\u0961\u0971-\u0977\u0979-\u097F\u0985-\u098C\u098F\u0990\u0993-\u09A8\u09AA-\u09B0\u09B2\u09B6-\u09B9\u09BD\u09CE\u09DC\u09DD\u09DF-\u09E1\u09F0\u09F1\u0A05-\u0A0A\u0A0F\u0A10\u0A13-\u0A28\u0A2A-\u0A30\u0A32\u0A33\u0A35\u0A36\u0A38\u0A39\u0A59-\u0A5C\u0A5E\u0A72-\u0A74\u0A85-\u0A8D\u0A8F-\u0A91\u0A93-\u0AA8\u0AAA-\u0AB0\u0AB2\u0AB3\u0AB5-\u0AB9\u0ABD\u0AD0\u0AE0\u0AE1\u0B05-\u0B0C\u0B0F\u0B10\u0B13-\u0B28\u0B2A-\u0B30\u0B32\u0B33\u0B35-\u0B39\u0B3D\u0B5C\u0B5D\u0B5F-\u0B61\u0B71\u0B83\u0B85-\u0B8A\u0B8E-\u0B90\u0B92-\u0B95\u0B99\u0B9A\u0B9C\u0B9E\u0B9F\u0BA3\u0BA4\u0BA8-\u0BAA\u0BAE-\u0BB9\u0BD0\u0C05-\u0C0C\u0C0E-\u0C10\u0C12-\u0C28\u0C2A-\u0C33\u0C35-\u0C39\u0C3D\u0C58\u0C59\u0C60\u0C61\u0C85-\u0C8C\u0C8E-\u0C90\u0C92-\u0CA8\u0CAA-\u0CB3\u0CB5-\u0CB9\u0CBD\u0CDE\u0CE0\u0CE1\u0CF1\u0CF2\u0D05-\u0D0C\u0D0E-\u0D10\u0D12-\u0D3A\u0D3D\u0D4E\u0D60\u0D61\u0D7A-\u0D7F\u0D85-\u0D96\u0D9A-\u0DB1\u0DB3-\u0DBB\u0DBD\u0DC0-\u0DC6\u0E01-\u0E30\u0E32\u0E33\u0E40-\u0E46\u0E81\u0E82\u0E84\u0E87\u0E88\u0E8A\u0E8D\u0E94-\u0E97\u0E99-\u0E9F\u0EA1-\u0EA3\u0EA5\u0EA7\u0EAA\u0EAB\u0EAD-\u0EB0\u0EB2\u0EB3\u0EBD\u0EC0-\u0EC4\u0EC6\u0EDC-\u0EDF\u0F00\u0F40-\u0F47\u0F49-\u0F6C\u0F88-\u0F8C\u1000-\u102A\u103F\u1050-\u1055\u105A-\u105D\u1061\u1065\u1066\u106E-\u1070\u1075-\u1081\u108E\u10A0-\u10C5\u10C7\u10CD\u10D0-\u10FA\u10FC-\u1248\u124A-\u124D\u1250-\u1256\u1258\u125A-\u125D\u1260-\u1288\u128A-\u128D\u1290-\u12B0\u12B2-\u12B5\u12B8-\u12BE\u12C0\u12C2-\u12C5\u12C8-\u12D6\u12D8-\u1310\u1312-\u1315\u1318-\u135A\u1380-\u138F\u13A0-\u13F4\u1401-\u166C\u166F-\u167F\u1681-\u169A\u16A0-\u16EA\u1700-\u170C\u170E-\u1711\u1720-\u1731\u1740-\u1751\u1760-\u176C\u176E-\u1770\u1780-\u17B3\u17D7\u17DC\u1820-\u1877\u1880-\u18A8\u18AA\u18B0-\u18F5\u1900-\u191C\u1950-\u196D\u1970-\u1974\u1980-\u19AB\u19C1-\u19C7\u1A00-\u1A16\u1A20-\u1A54\u1AA7\u1B05-\u1B33\u1B45-\u1B4B\u1B83-\u1BA0\u1BAE\u1BAF\u1BBA-\u1BE5\u1C00-\u1C23\u1C4D-\u1C4F\u1C5A-\u1C7D\u1CE9-\u1CEC\u1CEE-\u1CF1\u1CF5\u1CF6\u1D00-\u1DBF\u1E00-\u1F15\u1F18-\u1F1D\u1F20-\u1F45\u1F48-\u1F4D\u1F50-\u1F57\u1F59\u1F5B\u1F5D\u1F5F-\u1F7D\u1F80-\u1FB4\u1FB6-\u1FBC\u1FBE\u1FC2-\u1FC4\u1FC6-\u1FCC\u1FD0-\u1FD3\u1FD6-\u1FDB\u1FE0-\u1FEC\u1FF2-\u1FF4\u1FF6-\u1FFC\u2071\u207F\u2090-\u209C\u2102\u2107\u210A-\u2113\u2115\u2119-\u211D\u2124\u2126\u2128\u212A-\u212D\u212F-\u2139\u213C-\u213F\u2145-\u2149\u214E\u2183\u2184\u2C00-\u2C2E\u2C30-\u2C5E\u2C60-\u2CE4\u2CEB-\u2CEE\u2CF2\u2CF3\u2D00-\u2D25\u2D27\u2D2D\u2D30-\u2D67\u2D6F\u2D80-\u2D96\u2DA0-\u2DA6\u2DA8-\u2DAE\u2DB0-\u2DB6\u2DB8-\u2DBE\u2DC0-\u2DC6\u2DC8-\u2DCE\u2DD0-\u2DD6\u2DD8-\u2DDE\u2E2F\u3005\u3006\u3031-\u3035\u303B\u303C\u3041-\u3096\u309D-\u309F\u30A1-\u30FA\u30FC-\u30FF\u3105-\u312D\u3131-\u318E\u31A0-\u31BA\u31F0-\u31FF\u3400-\u4DB5\u4E00-\u9FCC\uA000-\uA48C\uA4D0-\uA4FD\uA500-\uA60C\uA610-\uA61F\uA62A\uA62B\uA640-\uA66E\uA67F-\uA697\uA6A0-\uA6E5\uA717-\uA71F\uA722-\uA788\uA78B-\uA78E\uA790-\uA793\uA7A0-\uA7AA\uA7F8-\uA801\uA803-\uA805\uA807-\uA80A\uA80C-\uA822\uA840-\uA873\uA882-\uA8B3\uA8F2-\uA8F7\uA8FB\uA90A-\uA925\uA930-\uA946\uA960-\uA97C\uA984-\uA9B2\uA9CF\uAA00-\uAA28\uAA40-\uAA42\uAA44-\uAA4B\uAA60-\uAA76\uAA7A\uAA80-\uAAAF\uAAB1\uAAB5\uAAB6\uAAB9-\uAABD\uAAC0\uAAC2\uAADB-\uAADD\uAAE0-\uAAEA\uAAF2-\uAAF4\uAB01-\uAB06\uAB09-\uAB0E\uAB11-\uAB16\uAB20-\uAB26\uAB28-\uAB2E\uABC0-\uABE2\uAC00-\uD7A3\uD7B0-\uD7C6\uD7CB-\uD7FB\uF900-\uFA6D\uFA70-\uFAD9\uFB00-\uFB06\uFB13-\uFB17\uFB1D\uFB1F-\uFB28\uFB2A-\uFB36\uFB38-\uFB3C\uFB3E\uFB40\uFB41\uFB43\uFB44\uFB46-\uFBB1\uFBD3-\uFD3D\uFD50-\uFD8F\uFD92-\uFDC7\uFDF0-\uFDFB\uFE70-\uFE74\uFE76-\uFEFC\uFF21-\uFF3A\uFF41-\uFF5A\uFF66-\uFFBE\uFFC2-\uFFC7\uFFCA-\uFFCF\uFFD2-\uFFD7\uFFDA-\uFFDC]/g;

// 2D Canvas drawing primitives.
function jsHasCtx2D(elem) {return !!elem.getContext;}
function jsGetCtx2D(elem) {return elem.getContext('2d');}
function jsBeginPath(ctx) {ctx.beginPath();}
function jsMoveTo(ctx, x, y) {ctx.moveTo(x, y);}
function jsLineTo(ctx, x, y) {ctx.lineTo(x, y);}
function jsStroke(ctx) {ctx.stroke();}
function jsFill(ctx) {ctx.fill();}
function jsRotate(ctx, radians) {ctx.rotate(radians);}
function jsTranslate(ctx, x, y) {ctx.translate(x, y);}
function jsScale(ctx, x, y) {ctx.scale(x, y);}
function jsPushState(ctx) {ctx.save();}
function jsPopState(ctx) {ctx.restore();}
function jsResetCanvas(el) {el.width = el.width;}
function jsDrawImage(ctx, img, x, y) {ctx.drawImage(img, x, y);}
function jsDrawImageClipped(ctx, img, x, y, cx, cy, cw, ch) {
    ctx.drawImage(img, cx, cy, cw, ch, x, y, cw, ch);
}
function jsDrawText(ctx, str, x, y) {ctx.fillText(str, x, y);}
function jsClip(ctx) {ctx.clip();}
function jsArc(ctx, x, y, radius, fromAngle, toAngle) {
    ctx.arc(x, y, radius, fromAngle, toAngle);
}
function jsCanvasToDataURL(el) {return el.toDataURL('image/png');}

// Simulate handles.
// When implementing new handles, remember that passed strings may be thunks,
// and so need to be evaluated before use.

function jsNewHandle(init, read, write, flush, close, seek, tell) {
    var h = {
        read: read || function() {},
        write: write || function() {},
        seek: seek || function() {},
        tell: tell || function() {},
        close: close || function() {},
        flush: flush || function() {}
    };
    init.call(h);
    return h;
}

function jsReadHandle(h, len) {return h.read(len);}
function jsWriteHandle(h, str) {return h.write(str);}
function jsFlushHandle(h) {return h.flush();}
function jsCloseHandle(h) {return h.close();}

function jsMkConWriter(op) {
    return function(str) {
        str = E(str);
        var lines = (this.buf + str).split('\n');
        for(var i = 0; i < lines.length-1; ++i) {
            op.call(console, lines[i]);
        }
        this.buf = lines[lines.length-1];
    }
}

function jsMkStdout() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(_) {return '';},
        jsMkConWriter(console.log),
        function() {console.log(this.buf); this.buf = '';}
    );
}

function jsMkStderr() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(_) {return '';},
        jsMkConWriter(console.warn),
        function() {console.warn(this.buf); this.buf = '';}
    );
}

function jsMkStdin() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(len) {
            while(this.buf.length < len) {
                this.buf += prompt('[stdin]') + '\n';
            }
            var ret = this.buf.substr(0, len);
            this.buf = this.buf.substr(len);
            return ret;
        }
    );
}

// "Weak Pointers". Mostly useless implementation since
// JS does its own GC.

function mkWeak(key, val, fin) {
    fin = !fin? function() {}: fin;
    return {key: key, val: val, fin: fin};
}

function derefWeak(w) {
    return [0, 1, E(w).val];
}

function finalizeWeak(w) {
    return [0, B(A(E(w).fin, [0]))];
}

/* For foreign import ccall "wrapper" */
function createAdjustor(args, f, a, b) {
    return function(){
        var x = f.apply(null, arguments);
        while(x instanceof F) {x = x.f();}
        return x;
    };
}

var __apply = function(f,as) {
    var arr = [];
    for(; as[0] === 1; as = as[2]) {
        arr.push(as[1]);
    }
    arr.reverse();
    return f.apply(null, arr);
}
var __app0 = function(f) {return f();}
var __app1 = function(f,a) {return f(a);}
var __app2 = function(f,a,b) {return f(a,b);}
var __app3 = function(f,a,b,c) {return f(a,b,c);}
var __app4 = function(f,a,b,c,d) {return f(a,b,c,d);}
var __app5 = function(f,a,b,c,d,e) {return f(a,b,c,d,e);}
var __jsNull = function() {return null;}
var __eq = function(a,b) {return a===b;}
var __createJSFunc = function(arity, f){
    if(f instanceof Function && arity === f.length) {
        return (function() {
            var x = f.apply(null,arguments);
            if(x instanceof T) {
                if(x.f !== __blackhole) {
                    var ff = x.f;
                    x.f = __blackhole;
                    return x.x = ff();
                }
                return x.x;
            } else {
                while(x instanceof F) {
                    x = x.f();
                }
                return E(x);
            }
        });
    } else {
        return (function(){
            var as = Array.prototype.slice.call(arguments);
            as.push(0);
            return E(B(A(f,as)));
        });
    }
}


function __arr2lst(elem,arr) {
    if(elem >= arr.length) {
        return [0];
    }
    return [1, arr[elem],new T(function(){return __arr2lst(elem+1,arr);})]
}

function __lst2arr(xs) {
    var arr = [];
    xs = E(xs);
    for(;xs[0] === 1; xs = E(xs[2])) {
        arr.push(E(xs[1]));
    }
    return arr;
}

var __new = function() {return ({});}
var __set = function(o,k,v) {o[k]=v;}
var __get = function(o,k) {return o[k];}
var __has = function(o,k) {return o[k]!==undefined;}

var _0="metaKey",_1="shiftKey",_2="altKey",_3="ctrlKey",_4="keyCode",_5=function(_6,_){var _7=_6[E(_4)],_8=_7,_9=_6[E(_3)],_a=_9,_b=_6[E(_2)],_c=_b,_d=_6[E(_1)],_e=_d,_f=_6[E(_0)],_g=_f;return new T(function(){var _h=Number(_8),_i=jsTrunc(_h);return [0,_i,E(_a),E(_c),E(_e),E(_g)];});},_j=function(_k,_l,_){return new F(function(){return _5(E(_l),_);});},_m="keydown",_n="keyup",_o="keypress",_p=function(_q){switch(E(_q)){case 0:return E(_o);case 1:return E(_n);default:return E(_m);}},_r=[0,_p,_j],_s="deltaZ",_t="deltaY",_u="deltaX",_v=function(_w,_x){var _y=E(_w);if(!_y[0]){return E(_x);}else{var _z=_y[2],_A=new T(function(){return B(_v(_z,_x));});return [1,_y[1],_A];}},_B=function(_C,_D){var _E=jsShowI(_C);return new F(function(){return _v(fromJSStr(_E),_D);});},_F=41,_G=40,_H=function(_I,_J,_K){if(_J>=0){return new F(function(){return _B(_J,_K);});}else{if(_I<=6){return new F(function(){return _B(_J,_K);});}else{var _L=new T(function(){var _M=jsShowI(_J);return B(_v(fromJSStr(_M),[1,_F,_K]));});return [1,_G,_L];}}},_N=new T(function(){return B(unCStr(")"));}),_O=new T(function(){return B(_H(0,2,_N));}),_P=new T(function(){return B(unAppCStr(") is outside of enumeration\'s range (0,",_O));}),_Q=function(_R){var _S=new T(function(){return B(_H(0,_R,_P));});return new F(function(){return err(B(unAppCStr("toEnum{MouseButton}: tag (",_S)));});},_T=function(_U,_){return new T(function(){var _V=Number(E(_U)),_W=jsTrunc(_V);if(_W<0){return B(_Q(_W));}else{if(_W>2){return B(_Q(_W));}else{return _W;}}});},_X=0,_Y=[0,_X,_X,_X],_Z="button",_10=new T(function(){return jsGetMouseCoords;}),_11=[0],_12=function(_13,_){var _14=E(_13);if(!_14[0]){return _11;}else{var _15=_14[1],_16=B(_12(_14[2],_)),_17=new T(function(){var _18=Number(E(_15));return jsTrunc(_18);});return [1,_17,_16];}},_19=function(_1a,_){var _1b=__arr2lst(0,_1a);return new F(function(){return _12(_1b,_);});},_1c=function(_1d,_){return new F(function(){return _19(E(_1d),_);});},_1e=function(_1f,_){return new T(function(){var _1g=Number(E(_1f));return jsTrunc(_1g);});},_1h=[0,_1e,_1c],_1i=function(_1j,_){var _1k=E(_1j);if(!_1k[0]){return _11;}else{var _1l=B(_1i(_1k[2],_));return [1,_1k[1],_1l];}},_1m=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_1n=new T(function(){return B(unCStr("base"));}),_1o=new T(function(){return B(unCStr("IOException"));}),_1p=new T(function(){var _1q=hs_wordToWord64(4053623282),_1r=hs_wordToWord64(3693590983);return [0,_1q,_1r,[0,_1q,_1r,_1n,_1m,_1o],_11,_11];}),_1s=function(_1t){return E(_1p);},_1u=function(_1v){return E(E(_1v)[1]);},_1w=function(_1x,_1y,_1z){var _1A=B(A(_1x,[_])),_1B=B(A(_1y,[_])),_1C=hs_eqWord64(_1A[1],_1B[1]);if(!_1C){return [0];}else{var _1D=hs_eqWord64(_1A[2],_1B[2]);return (!_1D)?[0]:[1,_1z];}},_1E=function(_1F){var _1G=E(_1F);return new F(function(){return _1w(B(_1u(_1G[1])),_1s,_1G[2]);});},_1H=new T(function(){return B(unCStr(": "));}),_1I=new T(function(){return B(unCStr(")"));}),_1J=new T(function(){return B(unCStr(" ("));}),_1K=new T(function(){return B(unCStr("interrupted"));}),_1L=new T(function(){return B(unCStr("system error"));}),_1M=new T(function(){return B(unCStr("unsatisified constraints"));}),_1N=new T(function(){return B(unCStr("user error"));}),_1O=new T(function(){return B(unCStr("permission denied"));}),_1P=new T(function(){return B(unCStr("illegal operation"));}),_1Q=new T(function(){return B(unCStr("end of file"));}),_1R=new T(function(){return B(unCStr("resource exhausted"));}),_1S=new T(function(){return B(unCStr("resource busy"));}),_1T=new T(function(){return B(unCStr("does not exist"));}),_1U=new T(function(){return B(unCStr("already exists"));}),_1V=new T(function(){return B(unCStr("resource vanished"));}),_1W=new T(function(){return B(unCStr("timeout"));}),_1X=new T(function(){return B(unCStr("unsupported operation"));}),_1Y=new T(function(){return B(unCStr("hardware fault"));}),_1Z=new T(function(){return B(unCStr("inappropriate type"));}),_20=new T(function(){return B(unCStr("invalid argument"));}),_21=new T(function(){return B(unCStr("failed"));}),_22=new T(function(){return B(unCStr("protocol error"));}),_23=function(_24,_25){switch(E(_24)){case 0:return new F(function(){return _v(_1U,_25);});break;case 1:return new F(function(){return _v(_1T,_25);});break;case 2:return new F(function(){return _v(_1S,_25);});break;case 3:return new F(function(){return _v(_1R,_25);});break;case 4:return new F(function(){return _v(_1Q,_25);});break;case 5:return new F(function(){return _v(_1P,_25);});break;case 6:return new F(function(){return _v(_1O,_25);});break;case 7:return new F(function(){return _v(_1N,_25);});break;case 8:return new F(function(){return _v(_1M,_25);});break;case 9:return new F(function(){return _v(_1L,_25);});break;case 10:return new F(function(){return _v(_22,_25);});break;case 11:return new F(function(){return _v(_21,_25);});break;case 12:return new F(function(){return _v(_20,_25);});break;case 13:return new F(function(){return _v(_1Z,_25);});break;case 14:return new F(function(){return _v(_1Y,_25);});break;case 15:return new F(function(){return _v(_1X,_25);});break;case 16:return new F(function(){return _v(_1W,_25);});break;case 17:return new F(function(){return _v(_1V,_25);});break;default:return new F(function(){return _v(_1K,_25);});}},_26=new T(function(){return B(unCStr("}"));}),_27=new T(function(){return B(unCStr("{handle: "));}),_28=function(_29,_2a,_2b,_2c,_2d,_2e){var _2f=new T(function(){var _2g=new T(function(){var _2h=new T(function(){var _2i=E(_2c);if(!_2i[0]){return E(_2e);}else{var _2j=new T(function(){var _2k=new T(function(){return B(_v(_1I,_2e));},1);return B(_v(_2i,_2k));},1);return B(_v(_1J,_2j));}},1);return B(_23(_2a,_2h));},1),_2l=E(_2b);if(!_2l[0]){return E(_2g);}else{var _2m=new T(function(){return B(_v(_1H,_2g));},1);return B(_v(_2l,_2m));}},1),_2n=E(_2d);if(!_2n[0]){var _2o=E(_29);if(!_2o[0]){return E(_2f);}else{var _2p=E(_2o[1]);if(!_2p[0]){var _2q=_2p[1],_2r=new T(function(){var _2s=new T(function(){var _2t=new T(function(){return B(_v(_1H,_2f));},1);return B(_v(_26,_2t));},1);return B(_v(_2q,_2s));},1);return new F(function(){return _v(_27,_2r);});}else{var _2u=_2p[1],_2v=new T(function(){var _2w=new T(function(){var _2x=new T(function(){return B(_v(_1H,_2f));},1);return B(_v(_26,_2x));},1);return B(_v(_2u,_2w));},1);return new F(function(){return _v(_27,_2v);});}}}else{var _2y=new T(function(){return B(_v(_1H,_2f));},1);return new F(function(){return _v(_2n[1],_2y);});}},_2z=function(_2A){var _2B=E(_2A);return new F(function(){return _28(_2B[1],_2B[2],_2B[3],_2B[4],_2B[6],_11);});},_2C=function(_2D,_2E,_2F){var _2G=E(_2E);return new F(function(){return _28(_2G[1],_2G[2],_2G[3],_2G[4],_2G[6],_2F);});},_2H=function(_2I,_2J){var _2K=E(_2I);return new F(function(){return _28(_2K[1],_2K[2],_2K[3],_2K[4],_2K[6],_2J);});},_2L=44,_2M=93,_2N=91,_2O=function(_2P,_2Q,_2R){var _2S=E(_2Q);if(!_2S[0]){return new F(function(){return unAppCStr("[]",_2R);});}else{var _2T=_2S[1],_2U=_2S[2],_2V=new T(function(){var _2W=new T(function(){var _2X=[1,_2M,_2R],_2Y=function(_2Z){var _30=E(_2Z);if(!_30[0]){return E(_2X);}else{var _31=_30[1],_32=_30[2],_33=new T(function(){var _34=new T(function(){return B(_2Y(_32));});return B(A(_2P,[_31,_34]));});return [1,_2L,_33];}};return B(_2Y(_2U));});return B(A(_2P,[_2T,_2W]));});return [1,_2N,_2V];}},_35=function(_36,_37){return new F(function(){return _2O(_2H,_36,_37);});},_38=[0,_2C,_2z,_35],_39=new T(function(){return [0,_1s,_38,_3a,_1E,_2z];}),_3a=function(_3b){return [0,_39,_3b];},_3c=[0],_3d=7,_3e=new T(function(){return B(unCStr("Pattern match failure in do expression at src/Haste/Prim/Any.hs:272:5-9"));}),_3f=[0,_3c,_3d,_11,_3e,_3c,_3c],_3g=new T(function(){return B(_3a(_3f));}),_3h=function(_){return new F(function(){return die(_3g);});},_3i=function(_3j){return E(E(_3j)[1]);},_3k=function(_3l,_3m,_3n,_){var _3o=__arr2lst(0,_3n),_3p=B(_1i(_3o,_)),_3q=E(_3p);if(!_3q[0]){return new F(function(){return _3h(_);});}else{var _3r=E(_3q[2]);if(!_3r[0]){return new F(function(){return _3h(_);});}else{if(!E(_3r[2])[0]){var _3s=B(A(_3i,[_3l,_3q[1],_])),_3t=B(A(_3i,[_3m,_3r[1],_]));return [0,_3s,_3t];}else{return new F(function(){return _3h(_);});}}}},_3u=function(_){return new F(function(){return __jsNull();});},_3v=function(_3w){var _3x=B(A(_3w,[_]));return E(_3x);},_3y=new T(function(){return B(_3v(_3u));}),_3z=new T(function(){return E(_3y);}),_3A=function(_3B,_3C,_){if(E(_3B)==7){var _3D=E(_10)(_3C),_3E=B(_3k(_1h,_1h,_3D,_)),_3F=_3E,_3G=_3C[E(_u)],_3H=_3G,_3I=_3C[E(_t)],_3J=_3I,_3K=_3C[E(_s)],_3L=_3K;return new T(function(){return [0,E(_3F),E(_3c),[0,_3H,_3J,_3L]];});}else{var _3M=E(_10)(_3C),_3N=B(_3k(_1h,_1h,_3M,_)),_3O=_3N,_3P=_3C[E(_Z)],_3Q=__eq(_3P,E(_3z));if(!E(_3Q)){var _3R=B(_T(_3P,_)),_3S=_3R;return new T(function(){return [0,E(_3O),[1,_3S],E(_Y)];});}else{return new T(function(){return [0,E(_3O),E(_3c),E(_Y)];});}}},_3T=function(_3U,_3V,_){return new F(function(){return _3A(_3U,E(_3V),_);});},_3W="mouseout",_3X="mouseover",_3Y="mousemove",_3Z="mouseup",_40="mousedown",_41="dblclick",_42="click",_43="wheel",_44=function(_45){switch(E(_45)){case 0:return E(_42);case 1:return E(_41);case 2:return E(_40);case 3:return E(_3Z);case 4:return E(_3Y);case 5:return E(_3X);case 6:return E(_3W);default:return E(_43);}},_46=[0,_44,_3T],_47=0,_48=function(_){return _47;},_49=function(_4a,_){return [1,_4a];},_4b=function(_4c){return E(_4c);},_4d=[0,_4b,_49],_4e=function(_4f,_4g,_){var _4h=B(A(_4f,[_])),_4i=B(A(_4g,[_]));return _4h;},_4j=function(_4k,_4l,_){var _4m=B(A(_4k,[_])),_4n=_4m,_4o=B(A(_4l,[_])),_4p=_4o;return new T(function(){return B(A(_4n,[_4p]));});},_4q=function(_4r,_4s,_){var _4t=B(A(_4s,[_]));return _4r;},_4u=function(_4v,_4w,_){var _4x=B(A(_4w,[_])),_4y=_4x;return new T(function(){return B(A(_4v,[_4y]));});},_4z=[0,_4u,_4q],_4A=function(_4B,_){return _4B;},_4C=function(_4D,_4E,_){var _4F=B(A(_4D,[_]));return new F(function(){return A(_4E,[_]);});},_4G=[0,_4z,_4A,_4j,_4C,_4e],_4H=function(_4I,_4J,_){var _4K=B(A(_4I,[_]));return new F(function(){return A(_4J,[_4K,_]);});},_4L=function(_4M){return [0,_3c,_3d,_11,_4M,_3c,_3c];},_4N=function(_4O,_){var _4P=new T(function(){var _4Q=new T(function(){return B(_4L(_4O));});return B(_3a(_4Q));});return new F(function(){return die(_4P);});},_4R=[0,_4G,_4H,_4C,_4A,_4N],_4S=[0,_4R,_4b],_4T=[0,_4S,_4A],_4U=function(_4V,_4W){return E(_4V)==E(_4W);},_4X=function(_4Y,_4Z){return E(_4Y)!=E(_4Z);},_50=[0,_4U,_4X],_51=function(_52,_53){var _54=E(_52),_55=E(_53);return (_54>_55)?E(_54):E(_55);},_56=function(_57,_58){var _59=E(_57),_5a=E(_58);return (_59>_5a)?E(_5a):E(_59);},_5b=function(_5c,_5d){return (_5c>=_5d)?(_5c!=_5d)?2:1:0;},_5e=function(_5f,_5g){return new F(function(){return _5b(E(_5f),E(_5g));});},_5h=function(_5i,_5j){return E(_5i)>=E(_5j);},_5k=function(_5l,_5m){return E(_5l)>E(_5m);},_5n=function(_5o,_5p){return E(_5o)<=E(_5p);},_5q=function(_5r,_5s){return E(_5r)<E(_5s);},_5t=[0,_50,_5e,_5q,_5n,_5k,_5h,_51,_56],_5u=function(_5v,_5w){while(1){var _5x=E(_5v);if(!_5x[0]){return (E(_5w)[0]==0)?1:0;}else{var _5y=E(_5w);if(!_5y[0]){return 2;}else{var _5z=E(_5x[1]),_5A=E(_5y[1]);if(_5z!=_5A){return (_5z>_5A)?2:0;}else{_5v=_5x[2];_5w=_5y[2];continue;}}}}},_5B=[1],_5C=new T(function(){return B(unCStr("Failure in Data.Map.balanceR"));}),_5D=function(_5E){return new F(function(){return err(_5C);});},_5F=new T(function(){return B(_5D(_));}),_5G=function(_5H,_5I,_5J,_5K){var _5L=E(_5J);if(!_5L[0]){var _5M=_5L[1],_5N=E(_5K);if(!_5N[0]){var _5O=_5N[1],_5P=_5N[2],_5Q=_5N[3];if(_5O<=(imul(3,_5M)|0)){return [0,(1+_5M|0)+_5O|0,E(_5H),_5I,E(_5L),E(_5N)];}else{var _5R=E(_5N[4]);if(!_5R[0]){var _5S=_5R[1],_5T=_5R[2],_5U=_5R[3],_5V=_5R[4],_5W=_5R[5],_5X=E(_5N[5]);if(!_5X[0]){var _5Y=_5X[1];if(_5S>=(imul(2,_5Y)|0)){var _5Z=function(_60){var _61=E(_5H),_62=E(_5W);return (_62[0]==0)?[0,(1+_5M|0)+_5O|0,E(_5T),_5U,[0,(1+_5M|0)+_60|0,E(_61),_5I,E(_5L),E(_5V)],[0,(1+_5Y|0)+_62[1]|0,E(_5P),_5Q,E(_62),E(_5X)]]:[0,(1+_5M|0)+_5O|0,E(_5T),_5U,[0,(1+_5M|0)+_60|0,E(_61),_5I,E(_5L),E(_5V)],[0,1+_5Y|0,E(_5P),_5Q,E(_5B),E(_5X)]];},_63=E(_5V);if(!_63[0]){return new F(function(){return _5Z(_63[1]);});}else{return new F(function(){return _5Z(0);});}}else{return [0,(1+_5M|0)+_5O|0,E(_5P),_5Q,[0,(1+_5M|0)+_5S|0,E(_5H),_5I,E(_5L),E(_5R)],E(_5X)];}}else{return E(_5F);}}else{return E(_5F);}}}else{return [0,1+_5M|0,E(_5H),_5I,E(_5L),E(_5B)];}}else{var _64=E(_5K);if(!_64[0]){var _65=_64[1],_66=_64[2],_67=_64[3],_68=_64[5],_69=E(_64[4]);if(!_69[0]){var _6a=_69[1],_6b=_69[2],_6c=_69[3],_6d=_69[4],_6e=_69[5],_6f=E(_68);if(!_6f[0]){var _6g=_6f[1];if(_6a>=(imul(2,_6g)|0)){var _6h=function(_6i){var _6j=E(_5H),_6k=E(_6e);return (_6k[0]==0)?[0,1+_65|0,E(_6b),_6c,[0,1+_6i|0,E(_6j),_5I,E(_5B),E(_6d)],[0,(1+_6g|0)+_6k[1]|0,E(_66),_67,E(_6k),E(_6f)]]:[0,1+_65|0,E(_6b),_6c,[0,1+_6i|0,E(_6j),_5I,E(_5B),E(_6d)],[0,1+_6g|0,E(_66),_67,E(_5B),E(_6f)]];},_6l=E(_6d);if(!_6l[0]){return new F(function(){return _6h(_6l[1]);});}else{return new F(function(){return _6h(0);});}}else{return [0,1+_65|0,E(_66),_67,[0,1+_6a|0,E(_5H),_5I,E(_5B),E(_69)],E(_6f)];}}else{return [0,3,E(_6b),_6c,[0,1,E(_5H),_5I,E(_5B),E(_5B)],[0,1,E(_66),_67,E(_5B),E(_5B)]];}}else{var _6m=E(_68);return (_6m[0]==0)?[0,3,E(_66),_67,[0,1,E(_5H),_5I,E(_5B),E(_5B)],E(_6m)]:[0,2,E(_5H),_5I,E(_5B),E(_64)];}}else{return [0,1,E(_5H),_5I,E(_5B),E(_5B)];}}},_6n=function(_6o,_6p){return [0,1,E(_6o),_6p,E(_5B),E(_5B)];},_6q=function(_6r,_6s,_6t){var _6u=E(_6t);if(!_6u[0]){return new F(function(){return _5G(_6u[2],_6u[3],_6u[4],B(_6q(_6r,_6s,_6u[5])));});}else{return new F(function(){return _6n(_6r,_6s);});}},_6v=new T(function(){return B(unCStr("Failure in Data.Map.balanceL"));}),_6w=function(_6x){return new F(function(){return err(_6v);});},_6y=new T(function(){return B(_6w(_));}),_6z=function(_6A,_6B,_6C,_6D){var _6E=E(_6D);if(!_6E[0]){var _6F=_6E[1],_6G=E(_6C);if(!_6G[0]){var _6H=_6G[1],_6I=_6G[2],_6J=_6G[3];if(_6H<=(imul(3,_6F)|0)){return [0,(1+_6H|0)+_6F|0,E(_6A),_6B,E(_6G),E(_6E)];}else{var _6K=E(_6G[4]);if(!_6K[0]){var _6L=_6K[1],_6M=E(_6G[5]);if(!_6M[0]){var _6N=_6M[1],_6O=_6M[2],_6P=_6M[3],_6Q=_6M[4],_6R=_6M[5];if(_6N>=(imul(2,_6L)|0)){var _6S=function(_6T){var _6U=E(_6R);return (_6U[0]==0)?[0,(1+_6H|0)+_6F|0,E(_6O),_6P,[0,(1+_6L|0)+_6T|0,E(_6I),_6J,E(_6K),E(_6Q)],[0,(1+_6F|0)+_6U[1]|0,E(_6A),_6B,E(_6U),E(_6E)]]:[0,(1+_6H|0)+_6F|0,E(_6O),_6P,[0,(1+_6L|0)+_6T|0,E(_6I),_6J,E(_6K),E(_6Q)],[0,1+_6F|0,E(_6A),_6B,E(_5B),E(_6E)]];},_6V=E(_6Q);if(!_6V[0]){return new F(function(){return _6S(_6V[1]);});}else{return new F(function(){return _6S(0);});}}else{return [0,(1+_6H|0)+_6F|0,E(_6I),_6J,E(_6K),[0,(1+_6F|0)+_6N|0,E(_6A),_6B,E(_6M),E(_6E)]];}}else{return E(_6y);}}else{return E(_6y);}}}else{return [0,1+_6F|0,E(_6A),_6B,E(_5B),E(_6E)];}}else{var _6W=E(_6C);if(!_6W[0]){var _6X=_6W[1],_6Y=_6W[2],_6Z=_6W[3],_70=_6W[5],_71=E(_6W[4]);if(!_71[0]){var _72=_71[1],_73=E(_70);if(!_73[0]){var _74=_73[1],_75=_73[2],_76=_73[3],_77=_73[4],_78=_73[5];if(_74>=(imul(2,_72)|0)){var _79=function(_7a){var _7b=E(_78);return (_7b[0]==0)?[0,1+_6X|0,E(_75),_76,[0,(1+_72|0)+_7a|0,E(_6Y),_6Z,E(_71),E(_77)],[0,1+_7b[1]|0,E(_6A),_6B,E(_7b),E(_5B)]]:[0,1+_6X|0,E(_75),_76,[0,(1+_72|0)+_7a|0,E(_6Y),_6Z,E(_71),E(_77)],[0,1,E(_6A),_6B,E(_5B),E(_5B)]];},_7c=E(_77);if(!_7c[0]){return new F(function(){return _79(_7c[1]);});}else{return new F(function(){return _79(0);});}}else{return [0,1+_6X|0,E(_6Y),_6Z,E(_71),[0,1+_74|0,E(_6A),_6B,E(_73),E(_5B)]];}}else{return [0,3,E(_6Y),_6Z,E(_71),[0,1,E(_6A),_6B,E(_5B),E(_5B)]];}}else{var _7d=E(_70);return (_7d[0]==0)?[0,3,E(_7d[2]),_7d[3],[0,1,E(_6Y),_6Z,E(_5B),E(_5B)],[0,1,E(_6A),_6B,E(_5B),E(_5B)]]:[0,2,E(_6A),_6B,E(_6W),E(_5B)];}}else{return [0,1,E(_6A),_6B,E(_5B),E(_5B)];}}},_7e=function(_7f,_7g,_7h){var _7i=E(_7h);if(!_7i[0]){return new F(function(){return _6z(_7i[2],_7i[3],B(_7e(_7f,_7g,_7i[4])),_7i[5]);});}else{return new F(function(){return _6n(_7f,_7g);});}},_7j=function(_7k,_7l,_7m,_7n,_7o,_7p,_7q){return new F(function(){return _6z(_7n,_7o,B(_7e(_7k,_7l,_7p)),_7q);});},_7r=function(_7s,_7t,_7u,_7v,_7w,_7x,_7y,_7z){var _7A=E(_7u);if(!_7A[0]){var _7B=_7A[1],_7C=_7A[2],_7D=_7A[3],_7E=_7A[4],_7F=_7A[5];if((imul(3,_7B)|0)>=_7v){if((imul(3,_7v)|0)>=_7B){return [0,(_7B+_7v|0)+1|0,E(_7s),_7t,E(_7A),[0,_7v,E(_7w),_7x,E(_7y),E(_7z)]];}else{return new F(function(){return _5G(_7C,_7D,_7E,B(_7r(_7s,_7t,_7F,_7v,_7w,_7x,_7y,_7z)));});}}else{return new F(function(){return _6z(_7w,_7x,B(_7G(_7s,_7t,_7B,_7C,_7D,_7E,_7F,_7y)),_7z);});}}else{return new F(function(){return _7j(_7s,_7t,_7v,_7w,_7x,_7y,_7z);});}},_7G=function(_7H,_7I,_7J,_7K,_7L,_7M,_7N,_7O){var _7P=E(_7O);if(!_7P[0]){var _7Q=_7P[1],_7R=_7P[2],_7S=_7P[3],_7T=_7P[4],_7U=_7P[5];if((imul(3,_7J)|0)>=_7Q){if((imul(3,_7Q)|0)>=_7J){return [0,(_7J+_7Q|0)+1|0,E(_7H),_7I,[0,_7J,E(_7K),_7L,E(_7M),E(_7N)],E(_7P)];}else{return new F(function(){return _5G(_7K,_7L,_7M,B(_7r(_7H,_7I,_7N,_7Q,_7R,_7S,_7T,_7U)));});}}else{return new F(function(){return _6z(_7R,_7S,B(_7G(_7H,_7I,_7J,_7K,_7L,_7M,_7N,_7T)),_7U);});}}else{return new F(function(){return _6q(_7H,_7I,[0,_7J,E(_7K),_7L,E(_7M),E(_7N)]);});}},_7V=function(_7W,_7X,_7Y,_7Z){var _80=E(_7Y);if(!_80[0]){var _81=_80[1],_82=_80[2],_83=_80[3],_84=_80[4],_85=_80[5],_86=E(_7Z);if(!_86[0]){var _87=_86[1],_88=_86[2],_89=_86[3],_8a=_86[4],_8b=_86[5];if((imul(3,_81)|0)>=_87){if((imul(3,_87)|0)>=_81){return [0,(_81+_87|0)+1|0,E(_7W),_7X,E(_80),E(_86)];}else{return new F(function(){return _5G(_82,_83,_84,B(_7r(_7W,_7X,_85,_87,_88,_89,_8a,_8b)));});}}else{return new F(function(){return _6z(_88,_89,B(_7G(_7W,_7X,_81,_82,_83,_84,_85,_8a)),_8b);});}}else{return new F(function(){return _6q(_7W,_7X,_80);});}}else{return new F(function(){return _7e(_7W,_7X,_7Z);});}},_8c=function(_8d,_8e,_8f,_8g){var _8h=E(_8d);if(_8h==1){var _8i=E(_8g);if(!_8i[0]){var _8j=new T(function(){return [0,1,E(_8e),_8f,E(_5B),E(_5B)];});return [0,_8j,_11,_11];}else{if(!B(_5u(_8e,E(_8i[1])[1]))){var _8k=new T(function(){return [0,1,E(_8e),_8f,E(_5B),E(_5B)];});return [0,_8k,_8i,_11];}else{var _8l=new T(function(){return [0,1,E(_8e),_8f,E(_5B),E(_5B)];});return [0,_8l,_11,_8i];}}}else{var _8m=B(_8c(_8h>>1,_8e,_8f,_8g)),_8n=_8m[1],_8o=_8m[3],_8p=E(_8m[2]);if(!_8p[0]){return [0,_8n,_11,_8o];}else{var _8q=E(_8p[1]),_8r=_8q[1],_8s=_8q[2],_8t=E(_8p[2]);if(!_8t[0]){var _8u=new T(function(){return B(_6q(_8r,_8s,_8n));});return [0,_8u,_11,_8o];}else{var _8v=E(_8t[1]),_8w=_8v[1];if(!B(_5u(_8r,_8w))){var _8x=B(_8c(_8h>>1,_8w,_8v[2],_8t[2])),_8y=_8x[1],_8z=new T(function(){return B(_7V(_8r,_8s,_8n,_8y));});return [0,_8z,_8x[2],_8x[3]];}else{return [0,_8n,_11,_8p];}}}}},_8A=function(_8B,_8C,_8D){var _8E=E(_8B),_8F=E(_8D);if(!_8F[0]){var _8G=_8F[2],_8H=_8F[3],_8I=_8F[4],_8J=_8F[5];switch(B(_5u(_8E,_8G))){case 0:return new F(function(){return _6z(_8G,_8H,B(_8A(_8E,_8C,_8I)),_8J);});break;case 1:return [0,_8F[1],E(_8E),_8C,E(_8I),E(_8J)];default:return new F(function(){return _5G(_8G,_8H,_8I,B(_8A(_8E,_8C,_8J)));});}}else{return [0,1,E(_8E),_8C,E(_5B),E(_5B)];}},_8K=function(_8L,_8M){while(1){var _8N=E(_8M);if(!_8N[0]){return E(_8L);}else{var _8O=E(_8N[1]),_8P=B(_8A(_8O[1],_8O[2],_8L));_8M=_8N[2];_8L=_8P;continue;}}},_8Q=function(_8R,_8S,_8T,_8U){return new F(function(){return _8K(B(_8A(_8S,_8T,_8R)),_8U);});},_8V=function(_8W,_8X,_8Y){var _8Z=E(_8X);return new F(function(){return _8K(B(_8A(_8Z[1],_8Z[2],_8W)),_8Y);});},_90=function(_91,_92,_93){while(1){var _94=E(_93);if(!_94[0]){return E(_92);}else{var _95=E(_94[1]),_96=_95[1],_97=_95[2],_98=E(_94[2]);if(!_98[0]){return new F(function(){return _6q(_96,_97,_92);});}else{var _99=E(_98[1]),_9a=_99[1];if(!B(_5u(_96,_9a))){var _9b=B(_8c(_91,_9a,_99[2],_98[2])),_9c=_9b[1],_9d=E(_9b[3]);if(!_9d[0]){var _9e=_91<<1,_9f=B(_7V(_96,_97,_92,_9c));_93=_9b[2];_91=_9e;_92=_9f;continue;}else{return new F(function(){return _8V(B(_7V(_96,_97,_92,_9c)),_9d[1],_9d[2]);});}}else{return new F(function(){return _8Q(_92,_96,_97,_98);});}}}}},_9g=function(_9h,_9i,_9j,_9k,_9l){var _9m=E(_9l);if(!_9m[0]){return new F(function(){return _6q(_9j,_9k,_9i);});}else{var _9n=E(_9m[1]),_9o=_9n[1];if(!B(_5u(_9j,_9o))){var _9p=B(_8c(_9h,_9o,_9n[2],_9m[2])),_9q=_9p[1],_9r=E(_9p[3]);if(!_9r[0]){return new F(function(){return _90(_9h<<1,B(_7V(_9j,_9k,_9i,_9q)),_9p[2]);});}else{return new F(function(){return _8V(B(_7V(_9j,_9k,_9i,_9q)),_9r[1],_9r[2]);});}}else{return new F(function(){return _8Q(_9i,_9j,_9k,_9m);});}}},_9s=function(_9t){var _9u=E(_9t);if(!_9u[0]){return [1];}else{var _9v=E(_9u[1]),_9w=_9v[1],_9x=_9v[2],_9y=E(_9u[2]);if(!_9y[0]){return [0,1,E(_9w),_9x,E(_5B),E(_5B)];}else{var _9z=_9y[2],_9A=E(_9y[1]),_9B=_9A[1],_9C=_9A[2];if(!B(_5u(_9w,_9B))){return new F(function(){return _9g(1,[0,1,E(_9w),_9x,E(_5B),E(_5B)],_9B,_9C,_9z);});}else{return new F(function(){return _8Q([0,1,E(_9w),_9x,E(_5B),E(_5B)],_9B,_9C,_9z);});}}}},_9D=new T(function(){return B(unCStr("}"));}),_9E=new T(function(){return B(unCStr(", "));}),_9F=new T(function(){return B(unCStr("Escape"));}),_9G=new T(function(){return B(unCStr("Defence"));}),_9H=new T(function(){return B(unCStr("Attack"));}),_9I=function(_9J){switch(E(_9J)){case 0:return E(_9H);case 1:return E(_9G);default:return E(_9F);}},_9K=function(_9L,_9M){switch(E(_9L)){case 0:return new F(function(){return _v(_9H,_9M);});break;case 1:return new F(function(){return _v(_9G,_9M);});break;default:return new F(function(){return _v(_9F,_9M);});}},_9N=function(_9O,_9P){return new F(function(){return _2O(_9K,_9O,_9P);});},_9Q=function(_9R,_9S,_9T){return new F(function(){return _9K(_9S,_9T);});},_9U=[0,_9Q,_9I,_9N],_9V=new T(function(){return B(unCStr("_commandMap = "));}),_9W=new T(function(){return B(unCStr("_listSize = "));}),_9X=new T(function(){return B(unCStr("_index = "));}),_9Y=new T(function(){return B(unCStr("CommandList {"));}),_9Z=function(_a0,_a1,_a2){var _a3=new T(function(){return B(A(_a1,[_a2]));});return new F(function(){return A(_a0,[[1,_2L,_a3]]);});},_a4=new T(function(){return B(unCStr("fromList "));}),_a5=new T(function(){return B(unCStr(": empty list"));}),_a6=new T(function(){return B(unCStr("Prelude."));}),_a7=function(_a8){var _a9=new T(function(){return B(_v(_a8,_a5));},1);return new F(function(){return err(B(_v(_a6,_a9)));});},_aa=new T(function(){return B(unCStr("foldr1"));}),_ab=new T(function(){return B(_a7(_aa));}),_ac=function(_ad,_ae){var _af=E(_ae);if(!_af[0]){return E(_ab);}else{var _ag=_af[1],_ah=E(_af[2]);if(!_ah[0]){return E(_ag);}else{var _ai=new T(function(){return B(_ac(_ad,_ah));});return new F(function(){return A(_ad,[_ag,_ai]);});}}},_aj=0,_ak=function(_al){return E(E(_al)[1]);},_am=function(_an,_ao){while(1){var _ap=(function(_aq,_ar){var _as=E(_ar);switch(_as[0]){case 0:var _at=_as[4],_au=new T(function(){return B(_am(_aq,_at));});_an=_au;_ao=_as[3];return null;case 1:return [1,[0,_as[1],_as[2]],_aq];default:return E(_aq);}})(_an,_ao);if(_ap!=null){return _ap;}}},_av=function(_aw){var _ax=E(_aw);if(!_ax[0]){var _ay=_ax[3],_az=_ax[4];if(_ax[2]>=0){var _aA=new T(function(){return B(_am(_11,_az));});return new F(function(){return _am(_aA,_ay);});}else{var _aB=new T(function(){return B(_am(_11,_ay));});return new F(function(){return _am(_aB,_az);});}}else{return new F(function(){return _am(_11,_ax);});}},_aC=function(_aD,_aE,_aF){var _aG=new T(function(){return B(_av(_aF));}),_aH=function(_aI,_aJ){var _aK=E(_aI),_aL=_aK[1],_aM=_aK[2],_aN=new T(function(){var _aO=new T(function(){return B(A(_ak,[_aD,_aj,_aM]));}),_aP=function(_aQ){return new F(function(){return _H(0,E(_aL),_aQ);});};return B(A(_ac,[_9Z,[1,_aP,[1,_aO,_11]],[1,_F,_aJ]]));});return [1,_G,_aN];};if(_aE<=10){var _aR=function(_aS){var _aT=new T(function(){return B(_2O(_aH,_aG,_aS));},1);return new F(function(){return _v(_a4,_aT);});};return E(_aR);}else{var _aU=function(_aV){var _aW=new T(function(){var _aX=new T(function(){return B(_2O(_aH,_aG,[1,_F,_aV]));},1);return B(_v(_a4,_aX));});return [1,_G,_aW];};return E(_aU);}},_aY=function(_aZ,_b0,_b1,_b2){var _b3=new T(function(){return B(_aC(_9U,0,_b2));}),_b4=function(_b5){var _b6=new T(function(){var _b7=new T(function(){var _b8=new T(function(){var _b9=new T(function(){var _ba=new T(function(){var _bb=new T(function(){var _bc=new T(function(){var _bd=new T(function(){var _be=new T(function(){return B(_v(_9D,_b5));});return B(A(_b3,[_be]));},1);return B(_v(_9V,_bd));},1);return B(_v(_9E,_bc));});return B(_H(0,E(_b1),_bb));},1);return B(_v(_9W,_ba));},1);return B(_v(_9E,_b9));});return B(_H(0,E(_b0),_b8));},1);return B(_v(_9X,_b7));},1);return new F(function(){return _v(_9Y,_b6);});};if(_aZ<11){return E(_b4);}else{var _bf=function(_bg){var _bh=new T(function(){return B(_b4([1,_F,_bg]));});return [1,_G,_bh];};return E(_bf);}},_bi=new T(function(){return B(unCStr("_commandList = "));}),_bj=new T(function(){return B(unCStr("_mp = "));}),_bk=new T(function(){return B(unCStr("_maxMP = "));}),_bl=new T(function(){return B(unCStr("_hp = "));}),_bm=new T(function(){return B(unCStr("_maxHP = "));}),_bn=new T(function(){return B(unCStr("_level = "));}),_bo=new T(function(){return B(unCStr("_luck = "));}),_bp=new T(function(){return B(unCStr("_agility = "));}),_bq=new T(function(){return B(unCStr("_vitality = "));}),_br=new T(function(){return B(unCStr("_technique = "));}),_bs=new T(function(){return B(unCStr("_intelligence = "));}),_bt=new T(function(){return B(unCStr("_strength = "));}),_bu=new T(function(){return B(unCStr("_name = "));}),_bv=new T(function(){return B(unCStr("Character {"));}),_bw=new T(function(){return B(unCStr("!!: negative index"));}),_bx=new T(function(){return B(_v(_a6,_bw));}),_by=new T(function(){return B(err(_bx));}),_bz=new T(function(){return B(unCStr("!!: index too large"));}),_bA=new T(function(){return B(_v(_a6,_bz));}),_bB=new T(function(){return B(err(_bA));}),_bC=function(_bD,_bE){while(1){var _bF=E(_bD);if(!_bF[0]){return E(_bB);}else{var _bG=E(_bE);if(!_bG){return E(_bF[1]);}else{_bD=_bF[2];_bE=_bG-1|0;continue;}}}},_bH=function(_bI,_bJ){if(_bJ>=0){return new F(function(){return _bC(_bI,_bJ);});}else{return E(_by);}},_bK=new T(function(){return B(unCStr("ACK"));}),_bL=new T(function(){return B(unCStr("BEL"));}),_bM=new T(function(){return B(unCStr("BS"));}),_bN=new T(function(){return B(unCStr("SP"));}),_bO=[1,_bN,_11],_bP=new T(function(){return B(unCStr("US"));}),_bQ=[1,_bP,_bO],_bR=new T(function(){return B(unCStr("RS"));}),_bS=[1,_bR,_bQ],_bT=new T(function(){return B(unCStr("GS"));}),_bU=[1,_bT,_bS],_bV=new T(function(){return B(unCStr("FS"));}),_bW=[1,_bV,_bU],_bX=new T(function(){return B(unCStr("ESC"));}),_bY=[1,_bX,_bW],_bZ=new T(function(){return B(unCStr("SUB"));}),_c0=[1,_bZ,_bY],_c1=new T(function(){return B(unCStr("EM"));}),_c2=[1,_c1,_c0],_c3=new T(function(){return B(unCStr("CAN"));}),_c4=[1,_c3,_c2],_c5=new T(function(){return B(unCStr("ETB"));}),_c6=[1,_c5,_c4],_c7=new T(function(){return B(unCStr("SYN"));}),_c8=[1,_c7,_c6],_c9=new T(function(){return B(unCStr("NAK"));}),_ca=[1,_c9,_c8],_cb=new T(function(){return B(unCStr("DC4"));}),_cc=[1,_cb,_ca],_cd=new T(function(){return B(unCStr("DC3"));}),_ce=[1,_cd,_cc],_cf=new T(function(){return B(unCStr("DC2"));}),_cg=[1,_cf,_ce],_ch=new T(function(){return B(unCStr("DC1"));}),_ci=[1,_ch,_cg],_cj=new T(function(){return B(unCStr("DLE"));}),_ck=[1,_cj,_ci],_cl=new T(function(){return B(unCStr("SI"));}),_cm=[1,_cl,_ck],_cn=new T(function(){return B(unCStr("SO"));}),_co=[1,_cn,_cm],_cp=new T(function(){return B(unCStr("CR"));}),_cq=[1,_cp,_co],_cr=new T(function(){return B(unCStr("FF"));}),_cs=[1,_cr,_cq],_ct=new T(function(){return B(unCStr("VT"));}),_cu=[1,_ct,_cs],_cv=new T(function(){return B(unCStr("LF"));}),_cw=[1,_cv,_cu],_cx=new T(function(){return B(unCStr("HT"));}),_cy=[1,_cx,_cw],_cz=[1,_bM,_cy],_cA=[1,_bL,_cz],_cB=[1,_bK,_cA],_cC=new T(function(){return B(unCStr("ENQ"));}),_cD=[1,_cC,_cB],_cE=new T(function(){return B(unCStr("EOT"));}),_cF=[1,_cE,_cD],_cG=new T(function(){return B(unCStr("ETX"));}),_cH=[1,_cG,_cF],_cI=new T(function(){return B(unCStr("STX"));}),_cJ=[1,_cI,_cH],_cK=new T(function(){return B(unCStr("SOH"));}),_cL=[1,_cK,_cJ],_cM=new T(function(){return B(unCStr("NUL"));}),_cN=[1,_cM,_cL],_cO=92,_cP=new T(function(){return B(unCStr("\\DEL"));}),_cQ=new T(function(){return B(unCStr("\\a"));}),_cR=new T(function(){return B(unCStr("\\\\"));}),_cS=new T(function(){return B(unCStr("\\SO"));}),_cT=new T(function(){return B(unCStr("\\r"));}),_cU=new T(function(){return B(unCStr("\\f"));}),_cV=new T(function(){return B(unCStr("\\v"));}),_cW=new T(function(){return B(unCStr("\\n"));}),_cX=new T(function(){return B(unCStr("\\t"));}),_cY=new T(function(){return B(unCStr("\\b"));}),_cZ=function(_d0,_d1){if(_d0<=127){var _d2=E(_d0);switch(_d2){case 92:return new F(function(){return _v(_cR,_d1);});break;case 127:return new F(function(){return _v(_cP,_d1);});break;default:if(_d2<32){var _d3=E(_d2);switch(_d3){case 7:return new F(function(){return _v(_cQ,_d1);});break;case 8:return new F(function(){return _v(_cY,_d1);});break;case 9:return new F(function(){return _v(_cX,_d1);});break;case 10:return new F(function(){return _v(_cW,_d1);});break;case 11:return new F(function(){return _v(_cV,_d1);});break;case 12:return new F(function(){return _v(_cU,_d1);});break;case 13:return new F(function(){return _v(_cT,_d1);});break;case 14:var _d4=new T(function(){var _d5=E(_d1);if(!_d5[0]){return [0];}else{if(E(_d5[1])==72){return B(unAppCStr("\\&",_d5));}else{return E(_d5);}}},1);return new F(function(){return _v(_cS,_d4);});break;default:var _d6=new T(function(){return B(_bH(_cN,_d3));});return new F(function(){return _v([1,_cO,_d6],_d1);});}}else{return [1,_d2,_d1];}}}else{var _d7=new T(function(){var _d8=jsShowI(_d0),_d9=new T(function(){var _da=E(_d1);if(!_da[0]){return [0];}else{var _db=E(_da[1]);if(_db<48){return E(_da);}else{if(_db>57){return E(_da);}else{return B(unAppCStr("\\&",_da));}}}},1);return B(_v(fromJSStr(_d8),_d9));});return [1,_cO,_d7];}},_dc=new T(function(){return B(unCStr("\\\""));}),_dd=function(_de,_df){var _dg=E(_de);if(!_dg[0]){return E(_df);}else{var _dh=_dg[2],_di=E(_dg[1]);if(_di==34){var _dj=new T(function(){return B(_dd(_dh,_df));},1);return new F(function(){return _v(_dc,_dj);});}else{var _dk=new T(function(){return B(_dd(_dh,_df));});return new F(function(){return _cZ(_di,_dk);});}}},_dl=34,_dm=function(_dn,_do,_dp,_dq,_dr,_ds,_dt,_du,_dv,_dw,_dx,_dy,_dz,_dA){var _dB=new T(function(){var _dC=E(_dA);return B(_aY(0,_dC[1],_dC[2],_dC[3]));}),_dD=function(_dE){var _dF=new T(function(){var _dG=new T(function(){var _dH=new T(function(){var _dI=new T(function(){var _dJ=new T(function(){var _dK=new T(function(){var _dL=new T(function(){var _dM=new T(function(){var _dN=new T(function(){var _dO=new T(function(){var _dP=new T(function(){var _dQ=new T(function(){var _dR=new T(function(){var _dS=new T(function(){var _dT=new T(function(){var _dU=new T(function(){var _dV=new T(function(){var _dW=new T(function(){var _dX=new T(function(){var _dY=new T(function(){var _dZ=new T(function(){var _e0=new T(function(){var _e1=new T(function(){var _e2=new T(function(){var _e3=new T(function(){var _e4=new T(function(){var _e5=new T(function(){var _e6=new T(function(){var _e7=new T(function(){var _e8=new T(function(){var _e9=new T(function(){var _ea=new T(function(){var _eb=new T(function(){var _ec=new T(function(){var _ed=new T(function(){var _ee=new T(function(){var _ef=new T(function(){var _eg=new T(function(){var _eh=new T(function(){return B(_v(_9D,_dE));});return B(A(_dB,[_eh]));},1);return B(_v(_bi,_eg));},1);return B(_v(_9E,_ef));});return B(_H(0,E(_dz),_ee));},1);return B(_v(_bj,_ed));},1);return B(_v(_9E,_ec));});return B(_H(0,E(_dy),_eb));},1);return B(_v(_bk,_ea));},1);return B(_v(_9E,_e9));});return B(_H(0,E(_dx),_e8));},1);return B(_v(_bl,_e7));},1);return B(_v(_9E,_e6));});return B(_H(0,E(_dw),_e5));},1);return B(_v(_bm,_e4));},1);return B(_v(_9E,_e3));});return B(_H(0,E(_dv),_e2));},1);return B(_v(_bn,_e1));},1);return B(_v(_9E,_e0));});return B(_H(0,E(_du),_dZ));},1);return B(_v(_bo,_dY));},1);return B(_v(_9E,_dX));});return B(_H(0,E(_dt),_dW));},1);return B(_v(_bp,_dV));},1);return B(_v(_9E,_dU));});return B(_H(0,E(_ds),_dT));},1);return B(_v(_bq,_dS));},1);return B(_v(_9E,_dR));});return B(_H(0,E(_dr),_dQ));},1);return B(_v(_br,_dP));},1);return B(_v(_9E,_dO));});return B(_H(0,E(_dq),_dN));},1);return B(_v(_bs,_dM));},1);return B(_v(_9E,_dL));});return B(_H(0,E(_dp),_dK));},1);return B(_v(_bt,_dJ));},1);return B(_v(_9E,_dI));});return B(_dd(_do,[1,_dl,_dH]));});return B(_v(_bu,[1,_dl,_dG]));},1);return new F(function(){return _v(_bv,_dF);});};if(_dn<11){return E(_dD);}else{var _ei=function(_ej){var _ek=new T(function(){return B(_dD([1,_F,_ej]));});return [1,_G,_ek];};return E(_ei);}},_el=function(_em){var _en=E(_em);return new F(function(){return _dm(0,_en[1],_en[2],_en[3],_en[4],_en[5],_en[6],_en[7],_en[8],_en[9],_en[10],_en[11],_en[12],_en[13]);});},_eo=new T(function(){return B(unCStr(" is not an element of the map"));}),_ep=function(_eq){var _er=new T(function(){return B(_v(B(_H(0,_eq,_11)),_eo));});return new F(function(){return err(B(unAppCStr("IntMap.!: key ",_er)));});},_es=function(_et,_eu){var _ev=_et;while(1){var _ew=E(_ev);switch(_ew[0]){case 0:var _ex=_ew[2]>>>0;if(((_eu>>>0&((_ex-1>>>0^4294967295)>>>0^_ex)>>>0)>>>0&4294967295)==_ew[1]){if(!((_eu>>>0&_ex)>>>0)){_ev=_ew[3];continue;}else{_ev=_ew[4];continue;}}else{return new F(function(){return _ep(_eu);});}break;case 1:if(_eu!=_ew[1]){return new F(function(){return _ep(_eu);});}else{return E(_ew[2]);}break;default:return new F(function(){return _ep(_eu);});}}},_ey=function(_ez,_eA){return new F(function(){return _es(_ez,E(_eA));});},_eB=0,_eC=function(_eD){var _eE=E(_eD);if(!_eE[0]){return [0,_11,_11];}else{var _eF=_eE[1],_eG=_eE[2],_eH=new T(function(){var _eI=B(_eC(_eG));return [0,_eI[1],_eI[2]];}),_eJ=new T(function(){return E(E(_eF)[13]);}),_eK=new T(function(){return E(E(_eH)[2]);}),_eL=new T(function(){var _eM=E(_eF),_eN=new T(function(){var _eO=E(_eJ),_eP=_eO[1],_eQ=_eO[2],_eR=new T(function(){var _eS=E(_eP);if(_eS!=(E(_eQ)-1|0)){return _eS+1|0;}else{return E(_eB);}});return [0,_eR,_eQ,_eO[3]];});return [0,_eM[1],_eM[2],_eM[3],_eM[4],_eM[5],_eM[6],_eM[7],_eM[8],_eM[9],_eM[10],_eM[11],_eM[12],_eN];}),_eT=new T(function(){return E(E(_eH)[1]);}),_eU=new T(function(){var _eV=E(_eJ);return B(_ey(_eV[3],_eV[1]));});return [0,[1,_eU,_eT],[1,_eL,_eK]];}},_eW=2,_eX=1,_eY=function(_eZ,_f0){return E(_f0);},_f1=function(_f2,_f3){return E(_f3);},_f4=[0,_f1,_eY],_f5=function(_f6,_f7){return E(_f6);},_f8=function(_f9){return E(_f9);},_fa=[0,_f8,_f5],_fb=function(_fc){return E(_fc);},_fd=function(_fe,_ff){while(1){var _fg=E(_ff);if(!_fg[0]){return [0];}else{var _fh=_fg[2],_fi=E(_fe);if(_fi==1){return E(_fh);}else{_fe=_fi-1|0;_ff=_fh;continue;}}}},_fj=function(_fk){return E(E(_fk)[1]);},_fl=function(_fm,_fn,_fo,_fp){var _fq=new T(function(){return E(_fm)-1|0;}),_fr=new T(function(){return 0<E(_fq);}),_fs=new T(function(){var _ft=E(_fm)+1|0;if(_ft>0){return B(_fd(_ft,_fp));}else{return E(_fp);}}),_fu=new T(function(){var _fv=new T(function(){return B(_bH(_fp,E(_fm)));});return B(A(_fo,[_fv]));}),_fw=function(_fx){var _fy=[1,_fx,_fs];if(!E(_fr)){return E(_fy);}else{var _fz=function(_fA,_fB){var _fC=E(_fA);if(!_fC[0]){return E(_fy);}else{var _fD=_fC[1],_fE=_fC[2],_fF=E(_fB);if(_fF==1){return [1,_fD,_fy];}else{var _fG=new T(function(){return B(_fz(_fE,_fF-1|0));});return [1,_fD,_fG];}}};return new F(function(){return _fz(_fp,E(_fq));});}};return new F(function(){return A(_fj,[_fn,_fw,_fu]);});},_fH=function(_fI,_fJ,_){while(1){var _fK=(function(_fL,_fM,_){var _fN=E(_fL);if(!_fN[0]){return [0,_47,_fM];}else{var _fO=_fN[2],_fP=E(_fN[1]),_fQ=_fP[2],_fR=E(_fP[1]);if(!_fR[0]){if(!E(_fR[1])){var _fS=new T(function(){var _fT=E(_fM),_fU=_fT[1],_fV=new T(function(){var _fW=function(_fX){var _fY=E(_fX),_fZ=_fY[10],_g0=new T(function(){return E(_fZ)-((imul(E(E(_fQ)[2]),5)|0)-(imul(E(B(_fl(_eB,_f4,_fb,_fU))[5]),2)|0)|0)|0;});return [0,_fY[1],_fY[2],_fY[3],_fY[4],_fY[5],_fY[6],_fY[7],_fY[8],_fY[9],_g0,_fY[11],_fY[12],_fY[13]];};return B(_fl(_eB,_fa,_fW,_fU));});return [0,_fV,_fT[2],_fT[3],_fT[4],_fT[5]];});_fI=_fO;_fJ=_fS;return null;}else{var _g1=new T(function(){var _g2=E(_fM),_g3=_g2[2],_g4=new T(function(){var _g5=function(_g6){var _g7=E(_g6),_g8=_g7[10],_g9=new T(function(){return E(_g8)-((imul(E(E(_fQ)[2]),5)|0)-(imul(E(B(_fl(_eB,_f4,_fb,_g3))[5]),2)|0)|0)|0;});return [0,_g7[1],_g7[2],_g7[3],_g7[4],_g7[5],_g7[6],_g7[7],_g7[8],_g7[9],_g9,_g7[11],_g7[12],_g7[13]];};return B(_fl(_eB,_fa,_g5,_g3));});return [0,_g2[1],_g4,_g2[3],_g2[4],_g2[5]];});_fI=_fO;_fJ=_g1;return null;}}else{_fI=_fO;var _ga=_fM;_fJ=_ga;return null;}}})(_fI,_fJ,_);if(_fK!=null){return _fK;}}},_gb=0,_gc=[0,_gb],_gd=function(_ge,_gf){var _gg=E(_ge);if(!_gg[0]){return [0];}else{var _gh=_gg[1],_gi=_gg[2],_gj=E(_gf);if(!_gj[0]){return [0];}else{var _gk=_gj[2],_gl=new T(function(){return B(_gd(_gi,_gk));}),_gm=new T(function(){var _gn=E(_gh);if(!_gn){return E(_gc);}else{return [1,_gn];}});return [1,[0,_gm,_gj[1]],_gl];}}},_go=function(_gp){while(1){var _gq=E(_gp);if(!_gq[0]){return true;}else{if(E(E(_gq[1])[10])>0){return false;}else{_gp=_gq[2];continue;}}}},_gr=function(_gs,_gt,_gu){var _gv=E(_gs),_gw=E(_gu);if(!_gw[0]){var _gx=_gw[2],_gy=_gw[3],_gz=_gw[4],_gA=_gw[5];switch(B(_5u(_gv,_gx))){case 0:return new F(function(){return _6z(_gx,_gy,B(_gr(_gv,_gt,_gz)),_gA);});break;case 1:return [0,_gw[1],E(_gv),_gt,E(_gz),E(_gA)];default:return new F(function(){return _5G(_gx,_gy,_gz,B(_gr(_gv,_gt,_gA)));});}}else{return [0,1,E(_gv),_gt,E(_5B),E(_5B)];}},_gB=function(_gC,_gD,_gE){var _gF=E(_gE);switch(_gF[0]){case 0:var _gG=_gF[1],_gH=_gF[2],_gI=_gF[3],_gJ=_gF[4],_gK=_gH>>>0;if(((_gC>>>0&((_gK-1>>>0^4294967295)>>>0^_gK)>>>0)>>>0&4294967295)==_gG){return ((_gC>>>0&_gK)>>>0==0)?[0,_gG,_gH,E(B(_gB(_gC,_gD,_gI))),E(_gJ)]:[0,_gG,_gH,E(_gI),E(B(_gB(_gC,_gD,_gJ)))];}else{var _gL=(_gC>>>0^_gG>>>0)>>>0,_gM=(_gL|_gL>>>1)>>>0,_gN=(_gM|_gM>>>2)>>>0,_gO=(_gN|_gN>>>4)>>>0,_gP=(_gO|_gO>>>8)>>>0,_gQ=(_gP|_gP>>>16)>>>0,_gR=(_gQ^_gQ>>>1)>>>0&4294967295,_gS=_gR>>>0;return ((_gC>>>0&_gS)>>>0==0)?[0,(_gC>>>0&((_gS-1>>>0^4294967295)>>>0^_gS)>>>0)>>>0&4294967295,_gR,[1,_gC,_gD],E(_gF)]:[0,(_gC>>>0&((_gS-1>>>0^4294967295)>>>0^_gS)>>>0)>>>0&4294967295,_gR,E(_gF),[1,_gC,_gD]];}break;case 1:var _gT=_gF[1];if(_gC!=_gT){var _gU=(_gC>>>0^_gT>>>0)>>>0,_gV=(_gU|_gU>>>1)>>>0,_gW=(_gV|_gV>>>2)>>>0,_gX=(_gW|_gW>>>4)>>>0,_gY=(_gX|_gX>>>8)>>>0,_gZ=(_gY|_gY>>>16)>>>0,_h0=(_gZ^_gZ>>>1)>>>0&4294967295,_h1=_h0>>>0;return ((_gC>>>0&_h1)>>>0==0)?[0,(_gC>>>0&((_h1-1>>>0^4294967295)>>>0^_h1)>>>0)>>>0&4294967295,_h0,[1,_gC,_gD],E(_gF)]:[0,(_gC>>>0&((_h1-1>>>0^4294967295)>>>0^_h1)>>>0)>>>0&4294967295,_h0,E(_gF),[1,_gC,_gD]];}else{return [1,_gC,_gD];}break;default:return [1,_gC,_gD];}},_h2=function(_h3,_h4){while(1){var _h5=(function(_h6,_h7){var _h8=E(_h7);if(!_h8[0]){var _h9=_h8[2],_ha=_h8[3],_hb=_h8[5],_hc=new T(function(){return B(_h2(_h6,_hb));}),_hd=new T(function(){var _he=E(_ha);return B(_es(_he[3],E(_he[1])));}),_hf=new T(function(){var _hg=E(_ha),_hh=_hg[1],_hi=_hg[2],_hj=new T(function(){var _hk=E(_hh);if(_hk!=(E(_hi)-1|0)){return _hk+1|0;}else{return E(_eB);}});return [0,_hj,_hi,_hg[3]];}),_hl=function(_hm,_){var _hn=new T(function(){var _ho=E(_hm),_hp=_ho[4],_hq=new T(function(){var _hr=new T(function(){return B(_gr(_h9,_hf,B(_es(_hp,0))));});return B(_gB(0,_hr,_hp));});return [0,_ho[1],_ho[2],_ho[3],_hq,_ho[5]];}),_hs=B(A(_hc,[_hn,_])),_ht=_hs,_hu=new T(function(){return E(E(_ht)[2]);}),_hv=new T(function(){return E(E(_ht)[1]);});return [0,[1,_hd,_hv],_hu];};_h3=_hl;_h4=_h8[4];return null;}else{return E(_h6);}})(_h3,_h4);if(_h5!=null){return _h5;}}},_hw=function(_hx){while(1){var _hy=E(_hx);if(!_hy[0]){return true;}else{if(E(E(_hy[1])[10])>0){return false;}else{_hx=_hy[2];continue;}}}},_hz=new T(function(){return B(unCStr("\n"));}),_hA=function(_hB,_hC,_){var _hD=jsWriteHandle(E(_hB),toJSStr(E(_hC)));return _47;},_hE=function(_hF,_hG,_){var _hH=E(_hF),_hI=jsWriteHandle(_hH,toJSStr(E(_hG)));return new F(function(){return _hA(_hH,_hz,_);});},_hJ=function(_hK,_hL){return new F(function(){return _5b(E(E(E(_hK)[2])[6]),E(E(E(_hL)[2])[6]));});},_hM=1,_hN=[0,_hM],_hO=function(_hP,_){return [0,_11,_hP];},_hQ=[1,_11,_11],_hR=function(_hS,_hT){var _hU=function(_hV,_hW){var _hX=E(_hV);if(!_hX[0]){return E(_hW);}else{var _hY=_hX[1],_hZ=_hX[2],_i0=E(_hW);if(!_i0[0]){return E(_hX);}else{var _i1=_i0[1],_i2=_i0[2];if(B(A(_hS,[_hY,_i1]))==2){var _i3=new T(function(){return B(_hU(_hX,_i2));});return [1,_i1,_i3];}else{var _i4=new T(function(){return B(_hU(_hZ,_i0));});return [1,_hY,_i4];}}}},_i5=function(_i6){var _i7=E(_i6);if(!_i7[0]){return [0];}else{var _i8=_i7[1],_i9=E(_i7[2]);if(!_i9[0]){return E(_i7);}else{var _ia=_i9[1],_ib=_i9[2],_ic=new T(function(){return B(_i5(_ib));}),_id=new T(function(){return B(_hU(_i8,_ia));});return [1,_id,_ic];}}},_ie=new T(function(){return B(_if(B(_i5(_11))));}),_if=function(_ig){while(1){var _ih=E(_ig);if(!_ih[0]){return E(_ie);}else{if(!E(_ih[2])[0]){return E(_ih[1]);}else{_ig=B(_i5(_ih));continue;}}}},_ii=new T(function(){return B(_ij(_11));}),_ik=function(_il,_im,_in){while(1){var _io=(function(_ip,_iq,_ir){var _is=E(_ir);if(!_is[0]){return [1,[1,_ip,_iq],_ii];}else{var _it=_is[1];if(B(A(_hS,[_ip,_it]))==2){_il=_it;var _iu=[1,_ip,_iq];_in=_is[2];_im=_iu;return null;}else{var _iv=new T(function(){return B(_ij(_is));});return [1,[1,_ip,_iq],_iv];}}})(_il,_im,_in);if(_io!=null){return _io;}}},_iw=function(_ix,_iy,_iz){while(1){var _iA=(function(_iB,_iC,_iD){var _iE=E(_iD);if(!_iE[0]){var _iF=new T(function(){return B(A(_iC,[[1,_iB,_11]]));});return [1,_iF,_ii];}else{var _iG=_iE[1],_iH=_iE[2];switch(B(A(_hS,[_iB,_iG]))){case 0:var _iI=function(_iJ){return new F(function(){return A(_iC,[[1,_iB,_iJ]]);});};_ix=_iG;_iy=_iI;_iz=_iH;return null;case 1:var _iK=function(_iL){return new F(function(){return A(_iC,[[1,_iB,_iL]]);});};_ix=_iG;_iy=_iK;_iz=_iH;return null;default:var _iM=new T(function(){return B(_ij(_iE));}),_iN=new T(function(){return B(A(_iC,[[1,_iB,_11]]));});return [1,_iN,_iM];}}})(_ix,_iy,_iz);if(_iA!=null){return _iA;}}},_ij=function(_iO){var _iP=E(_iO);if(!_iP[0]){return E(_hQ);}else{var _iQ=_iP[1],_iR=E(_iP[2]);if(!_iR[0]){return [1,_iP,_11];}else{var _iS=_iR[1],_iT=_iR[2];if(B(A(_hS,[_iQ,_iS]))==2){return new F(function(){return _ik(_iS,[1,_iQ,_11],_iT);});}else{var _iU=function(_iV){return [1,_iQ,_iV];};return new F(function(){return _iw(_iS,_iU,_iT);});}}}};return new F(function(){return _if(B(_ij(_hT)));});},_iW=function(_){return new F(function(){return jsMkStdout();});},_iX=new T(function(){return B(_3v(_iW));}),_iY=function(_iZ,_j0,_j1,_j2,_j3,_){var _j4=new T(function(){return E(_j1)+1|0;}),_j5=B(A(_h2,[_hO,B(_es(_j2,0)),[0,_iZ,_j0,_j4,_j2,_j3],_])),_j6=E(_j5),_j7=_j6[2],_j8=new T(function(){var _j9=B(_eC(E(_j7)[2]));return [0,_j9[1],_j9[2]];}),_ja=new T(function(){var _jb=E(_j7),_jc=new T(function(){return E(E(_j8)[2]);});return [0,_jb[1],_jc,_jb[3],_jb[4],_jb[5]];}),_jd=new T(function(){var _je=new T(function(){return E(E(_ja)[2]);},1);return B(_gd(E(_j8)[1],_je));}),_jf=function(_jg,_jh){var _ji=E(_jg);if(!_ji[0]){return E(_jd);}else{var _jj=_ji[1],_jk=_ji[2],_jl=E(_jh);if(!_jl[0]){return E(_jd);}else{var _jm=_jl[2],_jn=new T(function(){return B(_jf(_jk,_jm));}),_jo=new T(function(){var _jp=E(_jj);if(!_jp){return E(_hN);}else{return [1,_jp];}});return [1,[0,_jo,_jl[1]],_jn];}}},_jq=new T(function(){return E(E(_j7)[1]);},1),_jr=B(_fH(B(_hR(_hJ,B(_jf(_j6[1],_jq)))),_ja,_)),_js=E(E(_jr)[2]),_jt=_js[1],_ju=_js[2],_jv=_js[3],_jw=_js[4],_jx=B(_hE(_iX,B(_2O(_el,_jt,_11)),_)),_jy=B(_hE(_iX,B(_2O(_el,_ju,_11)),_));return (!B(_hw(_ju)))?(!B(_go(_jt)))?[0,_47,[0,_jt,_ju,_jv,_jw,_js[5]]]:[0,_47,[0,_jt,_ju,_jv,_jw,_eW]]:(!B(_go(_jt)))?[0,_47,[0,_jt,_ju,_jv,_jw,_eX]]:[0,_47,[0,_jt,_ju,_jv,_jw,_eW]];},_jz=function(_jA,_jB){if(_jA<=0){if(_jA>=0){return new F(function(){return quot(_jA,_jB);});}else{if(_jB<=0){return new F(function(){return quot(_jA,_jB);});}else{return quot(_jA+1|0,_jB)-1|0;}}}else{if(_jB>=0){if(_jA>=0){return new F(function(){return quot(_jA,_jB);});}else{if(_jB<=0){return new F(function(){return quot(_jA,_jB);});}else{return quot(_jA+1|0,_jB)-1|0;}}}else{return quot(_jA-1|0,_jB)-1|0;}}},_jC=new T(function(){return B(unCStr("GHC.Exception"));}),_jD=new T(function(){return B(unCStr("base"));}),_jE=new T(function(){return B(unCStr("ArithException"));}),_jF=new T(function(){var _jG=hs_wordToWord64(4194982440),_jH=hs_wordToWord64(3110813675);return [0,_jG,_jH,[0,_jG,_jH,_jD,_jC,_jE],_11,_11];}),_jI=function(_jJ){return E(_jF);},_jK=function(_jL){var _jM=E(_jL);return new F(function(){return _1w(B(_1u(_jM[1])),_jI,_jM[2]);});},_jN=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_jO=new T(function(){return B(unCStr("denormal"));}),_jP=new T(function(){return B(unCStr("divide by zero"));}),_jQ=new T(function(){return B(unCStr("loss of precision"));}),_jR=new T(function(){return B(unCStr("arithmetic underflow"));}),_jS=new T(function(){return B(unCStr("arithmetic overflow"));}),_jT=function(_jU,_jV){switch(E(_jU)){case 0:return new F(function(){return _v(_jS,_jV);});break;case 1:return new F(function(){return _v(_jR,_jV);});break;case 2:return new F(function(){return _v(_jQ,_jV);});break;case 3:return new F(function(){return _v(_jP,_jV);});break;case 4:return new F(function(){return _v(_jO,_jV);});break;default:return new F(function(){return _v(_jN,_jV);});}},_jW=function(_jX){return new F(function(){return _jT(_jX,_11);});},_jY=function(_jZ,_k0,_k1){return new F(function(){return _jT(_k0,_k1);});},_k2=function(_k3,_k4){return new F(function(){return _2O(_jT,_k3,_k4);});},_k5=[0,_jY,_jW,_k2],_k6=new T(function(){return [0,_jI,_k5,_k7,_jK,_jW];}),_k7=function(_k8){return [0,_k6,_k8];},_k9=3,_ka=new T(function(){return B(_k7(_k9));}),_kb=new T(function(){return die(_ka);}),_kc=0,_kd=new T(function(){return B(_k7(_kc));}),_ke=new T(function(){return die(_kd);}),_kf=function(_kg,_kh){var _ki=E(_kh);switch(_ki){case -1:var _kj=E(_kg);if(_kj==(-2147483648)){return E(_ke);}else{return new F(function(){return _jz(_kj,-1);});}break;case 0:return E(_kb);default:return new F(function(){return _jz(_kg,_ki);});}},_kk=new T(function(){return B(unCStr("%"));}),_kl=new T(function(){return B(unCStr("width"));}),_km=function(_kn){return E(E(_kn)[1]);},_ko=function(_kp){return E(E(_kp)[2]);},_kq=function(_kr,_ks,_kt,_ku,_kv){var _kw=function(_){var _kx=jsSetStyle(B(A(_km,[_kr,_kt])),toJSStr(E(_ku)),toJSStr(E(_kv)));return _47;};return new F(function(){return A(_ko,[_ks,_kw]);});},_ky=function(_kz,_kA,_){while(1){var _kB=(function(_kC,_kD,_){var _kE=E(_kC);if(!_kE[0]){return _47;}else{var _kF=E(_kD);if(!_kF[0]){return _47;}else{var _kG=_kF[1],_kH=new T(function(){var _kI=E(_kG);return B(_v(B(_H(0,B(_kf(imul(E(_kI[10]),100)|0,E(_kI[9]))),_11)),_kk));}),_kJ=B(A(_kq,[_4d,_4S,_kE[1],_kl,_kH,_]));_kz=_kE[2];_kA=_kF[2];return null;}}})(_kz,_kA,_);if(_kB!=null){return _kB;}}},_kK=function(_kL,_kM,_){while(1){var _kN=(function(_kO,_kP,_){var _kQ=E(_kO);if(!_kQ[0]){return _47;}else{var _kR=_kQ[2],_kS=E(_kP);if(!_kS[0]){return _47;}else{var _kT=_kS[2],_kU=E(_kS[1]),_kV=_kU[12],_kW=E(_kU[11]);if(!_kW){_kL=_kR;_kM=_kT;return null;}else{var _kX=new T(function(){var _kY=E(_kV),_kZ=E(_kW);if(_kZ==(-1)){var _l0=imul(_kY,100)|0;if(_l0==(-2147483648)){return E(_ke);}else{return B(_v(B(_H(0,B(_jz(_l0,-1)),_11)),_kk));}}else{return B(_v(B(_H(0,B(_jz(imul(_kY,100)|0,_kZ)),_11)),_kk));}}),_l1=B(A(_kq,[_4d,_4S,_kQ[1],_kl,_kX,_]));_kL=_kR;_kM=_kT;return null;}}}})(_kL,_kM,_);if(_kN!=null){return _kN;}}},_l2=new T(function(){return B(unCStr("innerHTML"));}),_l3=function(_l4,_l5,_l6,_l7,_l8){var _l9=function(_){var _la=jsSet(B(A(_km,[_l4,_l6])),toJSStr(E(_l7)),toJSStr(E(_l8)));return _47;};return new F(function(){return A(_ko,[_l5,_l9]);});},_lb=function(_lc,_ld,_){while(1){var _le=(function(_lf,_lg,_){var _lh=E(_lf);if(!_lh[0]){return _47;}else{var _li=E(_lg);if(!_li[0]){return _47;}else{var _lj=_li[1],_lk=new T(function(){return E(E(_lj)[1]);}),_ll=B(A(_l3,[_4d,_4S,_lh[1],_l2,_lk,_]));_lc=_lh[2];_ld=_li[2];return null;}}})(_lc,_ld,_);if(_le!=null){return _le;}}},_lm=function(_ln,_lo,_){while(1){var _lp=(function(_lq,_lr,_){var _ls=E(_lq);if(!_ls[0]){return _47;}else{var _lt=E(_lr);if(!_lt[0]){return _47;}else{var _lu=_lt[1],_lv=new T(function(){var _lw=E(_lu);return B(_v(B(_H(0,B(_kf(imul(E(_lw[10]),100)|0,E(_lw[9]))),_11)),_kk));}),_lx=B(A(_kq,[_4d,_4S,_ls[1],_kl,_lv,_]));_ln=_ls[2];_lo=_lt[2];return null;}}})(_ln,_lo,_);if(_lp!=null){return _lp;}}},_ly=new T(function(){return B(unCStr("#enemy-display-name"));}),_lz=new T(function(){return B(unCStr("enemy-chara"));}),_lA=35,_lB=[1,_lA,_lz],_lC=new T(function(){return B(unCStr("player-chara"));}),_lD=[1,_lA,_lC],_lE=new T(function(){return B(unCStr("#enemy-display-hpratio"));}),_lF=new T(function(){return B(unCStr("#player-display-mpratio"));}),_lG=function(_lH){return new F(function(){return _H(0,E(E(_lH)[11]),_11);});},_lI=new T(function(){return B(unCStr("#player-display-maxmp"));}),_lJ=function(_lK){return new F(function(){return _H(0,E(E(_lK)[12]),_11);});},_lL=new T(function(){return B(unCStr("#player-display-mp"));}),_lM=new T(function(){return B(unCStr("#player-display-hpratio"));}),_lN=function(_lO){return new F(function(){return _H(0,E(E(_lO)[9]),_11);});},_lP=new T(function(){return B(unCStr("#player-display-maxhp"));}),_lQ=function(_lR){return new F(function(){return _H(0,E(E(_lR)[10]),_11);});},_lS=new T(function(){return B(unCStr("#player-display-hp"));}),_lT=function(_lU){return E(E(_lU)[1]);},_lV=new T(function(){return B(unCStr("#player-display-name"));}),_lW=new T(function(){return B(unCStr("Control.Exception.Base"));}),_lX=new T(function(){return B(unCStr("base"));}),_lY=new T(function(){return B(unCStr("PatternMatchFail"));}),_lZ=new T(function(){var _m0=hs_wordToWord64(18445595),_m1=hs_wordToWord64(52003073);return [0,_m0,_m1,[0,_m0,_m1,_lX,_lW,_lY],_11,_11];}),_m2=function(_m3){return E(_lZ);},_m4=function(_m5){var _m6=E(_m5);return new F(function(){return _1w(B(_1u(_m6[1])),_m2,_m6[2]);});},_m7=function(_m8){return E(E(_m8)[1]);},_m9=function(_ma){return [0,_mb,_ma];},_mc=function(_md,_me){return new F(function(){return _v(E(_md)[1],_me);});},_mf=function(_mg,_mh){return new F(function(){return _2O(_mc,_mg,_mh);});},_mi=function(_mj,_mk,_ml){return new F(function(){return _v(E(_mk)[1],_ml);});},_mm=[0,_mi,_m7,_mf],_mb=new T(function(){return [0,_m2,_mm,_m9,_m4,_m7];}),_mn=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_mo=function(_mp){return E(E(_mp)[3]);},_mq=function(_mr,_ms){var _mt=new T(function(){return B(A(_mo,[_ms,_mr]));});return new F(function(){return die(_mt);});},_mu=function(_mv,_k8){return new F(function(){return _mq(_mv,_k8);});},_mw=function(_mx,_my){var _mz=E(_my);if(!_mz[0]){return [0,_11,_11];}else{var _mA=_mz[1],_mB=_mz[2];if(!B(A(_mx,[_mA]))){return [0,_11,_mz];}else{var _mC=new T(function(){var _mD=B(_mw(_mx,_mB));return [0,_mD[1],_mD[2]];}),_mE=new T(function(){return E(E(_mC)[2]);}),_mF=new T(function(){return E(E(_mC)[1]);});return [0,[1,_mA,_mF],_mE];}}},_mG=32,_mH=new T(function(){return B(unCStr("\n"));}),_mI=function(_mJ){return (E(_mJ)==124)?false:true;},_mK=function(_mL,_mM){var _mN=B(_mw(_mI,B(unCStr(_mL)))),_mO=_mN[1],_mP=function(_mQ,_mR){var _mS=new T(function(){var _mT=new T(function(){var _mU=new T(function(){return B(_v(_mR,_mH));},1);return B(_v(_mM,_mU));});return B(unAppCStr(": ",_mT));},1);return new F(function(){return _v(_mQ,_mS);});},_mV=E(_mN[2]);if(!_mV[0]){return new F(function(){return _mP(_mO,_11);});}else{if(E(_mV[1])==124){return new F(function(){return _mP(_mO,[1,_mG,_mV[2]]);});}else{return new F(function(){return _mP(_mO,_11);});}}},_mW=function(_mX){var _mY=new T(function(){return B(_mK(_mX,_mn));});return new F(function(){return _mu([0,_mY],_mb);});},_mZ=function(_n0){return new F(function(){return _mW("Main.hs:94:55-65|lambda");});},_n1=new T(function(){return B(_mZ(_));}),_n2=function(_n3,_n4,_){var _n5=jsQuerySelectorAll(_n3,toJSStr(_lD));if(!_n5[0]){return E(_n1);}else{var _n6=_n5[1];if(!E(_n5[2])[0]){var _n7=new T(function(){return E(E(_n4)[1]);}),_n8=function(_n9,_na,_){var _nb=jsQuerySelectorAll(E(_n6),toJSStr(E(_n9))),_nc=_nb,_nd=_n7,_=_;while(1){var _ne=(function(_nf,_ng,_){var _nh=E(_nf);if(!_nh[0]){return _47;}else{var _ni=E(_ng);if(!_ni[0]){return _47;}else{var _nj=_ni[1],_nk=new T(function(){return B(A(_na,[_nj]));}),_nl=B(A(_l3,[_4d,_4S,_nh[1],_l2,_nk,_]));_nc=_nh[2];_nd=_ni[2];return null;}}})(_nc,_nd,_);if(_ne!=null){return _ne;}}},_nm=B(_n8(_lV,_lT,_)),_nn=B(_n8(_lS,_lQ,_)),_no=B(_n8(_lP,_lN,_)),_np=E(_n6),_nq=jsQuerySelectorAll(_np,toJSStr(E(_lM))),_nr=B(_ky(_nq,_n7,_)),_ns=B(_n8(_lL,_lJ,_)),_nt=B(_n8(_lI,_lG,_)),_nu=jsQuerySelectorAll(_np,toJSStr(E(_lF))),_nv=B(_kK(_nu,_n7,_)),_nw=jsQuerySelectorAll(_n3,toJSStr(_lB));if(!_nw[0]){return E(_n1);}else{if(!E(_nw[2])[0]){var _nx=E(_nw[1]),_ny=jsQuerySelectorAll(_nx,toJSStr(E(_ly))),_nz=new T(function(){return E(E(_n4)[2]);},1),_nA=B(_lb(_ny,_nz,_)),_nB=jsQuerySelectorAll(_nx,toJSStr(E(_lE))),_nC=new T(function(){return E(E(_n4)[2]);},1);return new F(function(){return _lm(_nB,_nC,_);});}else{return E(_n1);}}}else{return E(_n1);}}},_nD=function(_nE){return E(E(_nE)[1]);},_nF=function(_nG){return E(E(_nG)[2]);},_nH=function(_nI){return new F(function(){return fromJSStr(E(_nI));});},_nJ=function(_nK,_nL,_nM,_nN){var _nO=function(_){return new F(function(){return jsGet(B(A(_km,[_nK,_nM])),E(_nN));});};return new F(function(){return A(_ko,[_nL,_nO]);});},_nP=function(_nQ){return E(E(_nQ)[4]);},_nR=function(_nS,_nT,_nU,_nV){var _nW=B(_nD(_nT)),_nX=new T(function(){return B(_nP(_nW));}),_nY=function(_nZ){var _o0=new T(function(){return B(_nH(_nZ));});return new F(function(){return A(_nX,[_o0]);});},_o1=new T(function(){var _o2=new T(function(){return toJSStr(E(_nV));});return B(_nJ(_nS,_nT,_nU,_o2));});return new F(function(){return A(_nF,[_nW,_o1,_nY]);});},_o3=function(_o4,_o5,_){var _o6=B(A(_nR,[_4d,_4S,_o4,_l2,_])),_o7=_o6,_o8=new T(function(){return B(_v(_o7,_o5));});return new F(function(){return A(_l3,[_4d,_4S,_o4,_l2,_o8,_]);});},_o9=new T(function(){return B(unCStr("  <div class=\"enemy\">"));}),_oa=new T(function(){return B(unCStr("    <span id=\"enemy-display-name\"></span><br>"));}),_ob=new T(function(){return B(unCStr("    HP"));}),_oc=new T(function(){return B(unCStr("    <div class=\"progress\">"));}),_od=new T(function(){return B(unCStr("      <div class=\"progress-bar\" role=\"progressbar\" id=\"enemy-display-hpratio\">"));}),_oe=new T(function(){return B(unCStr("      </div>"));}),_of=new T(function(){return B(unCStr("    </div>"));}),_og=new T(function(){return B(unCStr("</div>"));}),_oh=[1,_og,_11],_oi=new T(function(){return B(unCStr("  </div>"));}),_oj=[1,_oi,_oh],_ok=[1,_of,_oj],_ol=[1,_oe,_ok],_om=[1,_od,_ol],_on=[1,_oc,_om],_oo=[1,_ob,_on],_op=[1,_oa,_oo],_oq=[1,_o9,_op],_or=new T(function(){return B(unCStr("<div class=\"col-md-4\">"));}),_os=function(_ot){var _ou=E(_ot);if(!_ou[0]){return [0];}else{var _ov=_ou[2],_ow=new T(function(){return B(_os(_ov));},1);return new F(function(){return _v(_ou[1],_ow);});}},_ox=function(_oy,_oz){var _oA=new T(function(){return B(_os(_oz));},1);return new F(function(){return _v(_oy,_oA);});},_oB=new T(function(){return B(_ox(_or,_oq));}),_oC=new T(function(){return B(unCStr("  <div class=\"player\">"));}),_oD=new T(function(){return B(unCStr("    <span id=\"player-display-name\"></span><br>"));}),_oE=new T(function(){return B(unCStr("    HP <span id=\"player-display-hp\"></span> / <span id=\"player-display-maxhp\"></span>"));}),_oF=new T(function(){return B(unCStr("      <div class=\"progress-bar\" role=\"progressbar\" id=\"player-display-hpratio\">"));}),_oG=new T(function(){return B(unCStr("      <div class=\"progress-bar progress-bar-info\" role=\"progressbar\" id=\"player-display-mpratio\">"));}),_oH=[1,_oG,_ol],_oI=[1,_oc,_oH],_oJ=new T(function(){return B(unCStr("    MP <span id=\"player-display-mp\"></span> / <span id=\"player-display-maxmp\"></span>"));}),_oK=[1,_oJ,_oI],_oL=[1,_of,_oK],_oM=[1,_oe,_oL],_oN=[1,_oF,_oM],_oO=[1,_oc,_oN],_oP=[1,_oE,_oO],_oQ=[1,_oD,_oP],_oR=[1,_oC,_oQ],_oS=function(_oT){var _oU=E(_oT);if(!_oU[0]){return [0];}else{var _oV=_oU[2],_oW=new T(function(){return B(_oS(_oV));},1);return new F(function(){return _v(_oU[1],_oW);});}},_oX=function(_oY,_oZ){var _p0=new T(function(){return B(_oS(_oZ));},1);return new F(function(){return _v(_oY,_p0);});},_p1=new T(function(){return B(_oX(_or,_oR));}),_p2=function(_p3,_p4,_){var _p5=rMV(_p4),_p6=E(_p3),_p7=jsQuerySelectorAll(_p6,toJSStr(_lD));if(!_p7[0]){return E(_n1);}else{var _p8=_p7[1];if(!E(_p7[2])[0]){var _p9=B(A(_l3,[_4d,_4S,_p8,_l2,_11,_])),_pa=E(E(_p5)[7]),_pb=function(_pc,_){while(1){var _pd=E(_pc);if(!_pd[0]){return _47;}else{var _pe=B(_o3(_p8,_p1,_));_pc=_pd[2];continue;}}},_pf=B(_pb(_pa[1],_)),_pg=jsQuerySelectorAll(_p6,toJSStr(_lB));if(!_pg[0]){return E(_n1);}else{var _ph=_pg[1];if(!E(_pg[2])[0]){var _pi=B(A(_l3,[_4d,_4S,_ph,_l2,_11,_])),_pj=function(_pk,_){while(1){var _pl=E(_pk);if(!_pl[0]){return _47;}else{var _pm=B(_o3(_ph,_oB,_));_pk=_pl[2];continue;}}},_pn=B(_pj(_pa[2],_));return new F(function(){return _n2(_p6,_pa,_);});}else{return E(_n1);}}}else{return E(_n1);}}},_po=function(_pp,_pq,_pr,_ps){return (_pp!=_pr)?true:(E(_pq)!=E(_ps))?true:false;},_pt=function(_pu,_pv){var _pw=E(_pu),_px=E(_pv);return new F(function(){return _po(E(_pw[1]),_pw[2],E(_px[1]),_px[2]);});},_py=function(_pz,_pA,_pB,_pC){if(_pz!=_pB){return false;}else{return new F(function(){return _4U(_pA,_pC);});}},_pD=function(_pE,_pF){var _pG=E(_pE),_pH=E(_pF);return new F(function(){return _py(E(_pG[1]),_pG[2],E(_pH[1]),_pH[2]);});},_pI=[0,_pD,_pt],_pJ=function(_pK,_pL,_pM,_pN){if(_pK>=_pM){if(_pK!=_pM){return 2;}else{return new F(function(){return _5e(_pL,_pN);});}}else{return 0;}},_pO=function(_pP,_pQ){var _pR=E(_pP),_pS=E(_pQ);return new F(function(){return _pJ(E(_pR[1]),_pR[2],E(_pS[1]),_pS[2]);});},_pT=function(_pU,_pV,_pW,_pX){if(_pU>=_pW){if(_pU!=_pW){return false;}else{return new F(function(){return _5q(_pV,_pX);});}}else{return true;}},_pY=function(_pZ,_q0){var _q1=E(_pZ),_q2=E(_q0);return new F(function(){return _pT(E(_q1[1]),_q1[2],E(_q2[1]),_q2[2]);});},_q3=function(_q4,_q5,_q6,_q7){if(_q4>=_q6){if(_q4!=_q6){return false;}else{return new F(function(){return _5n(_q5,_q7);});}}else{return true;}},_q8=function(_q9,_qa){var _qb=E(_q9),_qc=E(_qa);return new F(function(){return _q3(E(_qb[1]),_qb[2],E(_qc[1]),_qc[2]);});},_qd=function(_qe,_qf,_qg,_qh){if(_qe>=_qg){if(_qe!=_qg){return true;}else{return new F(function(){return _5k(_qf,_qh);});}}else{return false;}},_qi=function(_qj,_qk){var _ql=E(_qj),_qm=E(_qk);return new F(function(){return _qd(E(_ql[1]),_ql[2],E(_qm[1]),_qm[2]);});},_qn=function(_qo,_qp,_qq,_qr){if(_qo>=_qq){if(_qo!=_qq){return true;}else{return new F(function(){return _5h(_qp,_qr);});}}else{return false;}},_qs=function(_qt,_qu){var _qv=E(_qt),_qw=E(_qu);return new F(function(){return _qn(E(_qv[1]),_qv[2],E(_qw[1]),_qw[2]);});},_qx=function(_qy,_qz){var _qA=E(_qy),_qB=E(_qA[1]),_qC=E(_qz),_qD=E(_qC[1]);return (_qB>=_qD)?(_qB!=_qD)?E(_qA):(E(_qA[2])>E(_qC[2]))?E(_qA):E(_qC):E(_qC);},_qE=function(_qF,_qG){var _qH=E(_qF),_qI=E(_qH[1]),_qJ=E(_qG),_qK=E(_qJ[1]);return (_qI>=_qK)?(_qI!=_qK)?E(_qJ):(E(_qH[2])>E(_qJ[2]))?E(_qJ):E(_qH):E(_qH);},_qL=[0,_pI,_pO,_pY,_q8,_qi,_qs,_qx,_qE],_qM=new T(function(){return B(unCStr("Map.!: given key is not an element in the map"));}),_qN=new T(function(){return B(err(_qM));}),_qO=function(_qP,_qQ,_qR){while(1){var _qS=E(_qR);if(!_qS[0]){var _qT=_qS[4],_qU=_qS[5],_qV=E(_qS[2]),_qW=E(_qV[1]);if(_qP>=_qW){if(_qP!=_qW){_qR=_qU;continue;}else{var _qX=E(_qV[2]);if(_qQ>=_qX){if(_qQ!=_qX){_qR=_qU;continue;}else{return E(_qS[3]);}}else{_qR=_qT;continue;}}}else{_qR=_qT;continue;}}else{return E(_qN);}}},_qY=function(_qZ,_r0,_r1,_){var _r2=B(A(_r0,[_r1,_])),_r3=_r2,_r4=new T(function(){return E(E(_r3)[2]);});return [0,_qZ,_r4];},_r5=function(_r6,_r7,_r8,_){var _r9=B(A(_r7,[_r8,_])),_ra=_r9,_rb=new T(function(){return E(E(_ra)[2]);}),_rc=new T(function(){var _rd=new T(function(){return E(E(_ra)[1]);});return B(A(_r6,[_rd]));});return [0,_rc,_rb];},_re=[0,_r5,_qY],_rf=function(_rg,_rh,_ri,_){var _rj=B(A(_rg,[_ri,_])),_rk=_rj,_rl=new T(function(){return E(E(_rk)[2]);}),_rm=B(A(_rh,[_rl,_])),_rn=_rm,_ro=new T(function(){return E(E(_rn)[2]);}),_rp=new T(function(){var _rq=new T(function(){return E(E(_rn)[1]);});return B(A(E(_rk)[1],[_rq]));});return [0,_rp,_ro];},_rr=function(_rs,_rt,_ru,_){var _rv=B(A(_rs,[_ru,_])),_rw=_rv,_rx=new T(function(){return E(E(_rw)[2]);}),_ry=B(A(_rt,[_rx,_])),_rz=_ry,_rA=new T(function(){return E(E(_rz)[2]);}),_rB=new T(function(){return E(E(_rz)[1]);});return [0,_rB,_rA];},_rC=function(_rD,_rE,_rF,_){var _rG=B(A(_rD,[_rF,_])),_rH=_rG,_rI=new T(function(){return E(E(_rH)[2]);}),_rJ=B(A(_rE,[_rI,_])),_rK=_rJ,_rL=new T(function(){return E(E(_rK)[2]);}),_rM=new T(function(){return E(E(_rH)[1]);});return [0,_rM,_rL];},_rN=function(_rO,_rP,_){return [0,_rO,_rP];},_rQ=[0,_re,_rN,_rf,_rr,_rC],_rR=function(_rS,_rT,_){return new F(function(){return _4N(_rS,_);});},_rU=function(_rV,_rW,_rX,_){var _rY=B(A(_rV,[_rX,_])),_rZ=_rY,_s0=new T(function(){return E(E(_rZ)[2]);}),_s1=new T(function(){return E(E(_rZ)[1]);});return new F(function(){return A(_rW,[_s1,_s0,_]);});},_s2=function(_s3,_s4,_s5,_s6,_s7){var _s8=function(_s9){var _sa=new T(function(){return E(E(_s9)[2]);}),_sb=new T(function(){return E(E(_s9)[1]);});return new F(function(){return A(_s6,[_sb,_sa]);});},_sc=new T(function(){return B(A(_s5,[_s7]));});return new F(function(){return A(_nF,[_s4,_sc,_s8]);});},_sd=function(_se){return E(E(_se)[5]);},_sf=function(_sg,_sh,_si){var _sj=new T(function(){return B(A(_sd,[_sh,_si]));}),_sk=function(_sl){return E(_sj);};return E(_sk);},_sm=function(_sn,_so){var _sp=function(_sq){return new F(function(){return _sf(_sn,_so,_sq);});},_sr=function(_ss,_st){return new F(function(){return A(_nP,[_so,[0,_ss,_st]]);});},_su=function(_sv,_sq){return new F(function(){return _sw(_sn,_so,_sv,_sq);});},_sx=function(_sy,_sv,_sq){return new F(function(){return _s2(_sn,_so,_sy,_sv,_sq);});};return [0,_sn,_sx,_su,_sr,_sp];},_sw=function(_sz,_sA,_sB,_sC){var _sD=function(_sE){return E(_sC);};return new F(function(){return A(_nF,[B(_sm(_sz,_sA)),_sB,_sD]);});},_sF=function(_sG,_sH){return new F(function(){return _sw(_rQ,_4R,_sG,_sH);});},_sI=[0,_rQ,_rU,_sF,_rN,_rR],_sJ=function(_sK,_sL,_){var _sM=B(A(_sK,[_]));return [0,_sM,_sL];},_sN=[0,_sI,_sJ],_sO=function(_){return new F(function(){return _mW("Main.hs:(425,72)-(427,42)|lambda");});},_sP=function(_sQ,_sR,_sS,_){while(1){var _sT=(function(_sU,_sV,_sW,_){var _sX=E(_sU);if(!_sX[0]){return [0,_47,_sW];}else{var _sY=E(_sV);if(!_sY[0]){return [0,_47,_sW];}else{var _sZ=_sY[1],_t0=new T(function(){var _t1=E(_sZ);return B(_v(B(_H(0,B(_kf(imul(E(_t1[10]),100)|0,E(_t1[9]))),_11)),_kk));}),_t2=B(A(_kq,[_4d,_sN,_sX[1],_kl,_t0,_sW,_])),_t3=_t2,_t4=new T(function(){return E(E(_t3)[2]);});_sQ=_sX[2];_sR=_sY[2];_sS=_t4;return null;}}})(_sQ,_sR,_sS,_);if(_sT!=null){return _sT;}}},_t5=function(_t6,_t7,_t8,_){while(1){var _t9=(function(_ta,_tb,_tc,_){var _td=E(_ta);if(!_td[0]){return [0,_47,_tc];}else{var _te=_td[2],_tf=E(_tb);if(!_tf[0]){return [0,_47,_tc];}else{var _tg=_tf[2],_th=E(_tf[1]),_ti=_th[12],_tj=E(_th[11]);if(!_tj){_t6=_te;_t7=_tg;var _tk=_tc;_t8=_tk;return null;}else{var _tl=new T(function(){var _tm=E(_ti),_tn=E(_tj);if(_tn==(-1)){var _to=imul(_tm,100)|0;if(_to==(-2147483648)){return E(_ke);}else{return B(_v(B(_H(0,B(_jz(_to,-1)),_11)),_kk));}}else{return B(_v(B(_H(0,B(_jz(imul(_tm,100)|0,_tn)),_11)),_kk));}}),_tp=B(A(_kq,[_4d,_sN,_td[1],_kl,_tl,_tc,_])),_tq=_tp,_tr=new T(function(){return E(E(_tq)[2]);});_t6=_te;_t7=_tg;_t8=_tr;return null;}}}})(_t6,_t7,_t8,_);if(_t9!=null){return _t9;}}},_ts=function(_tt,_tu,_tv,_){while(1){var _tw=(function(_tx,_ty,_tz,_){var _tA=E(_tx);if(!_tA[0]){return [0,_47,_tz];}else{var _tB=E(_ty);if(!_tB[0]){return [0,_47,_tz];}else{var _tC=_tB[1],_tD=new T(function(){return E(E(_tC)[1]);}),_tE=B(A(_l3,[_4d,_sN,_tA[1],_l2,_tD,_tz,_])),_tF=_tE,_tG=new T(function(){return E(E(_tF)[2]);});_tt=_tA[2];_tu=_tB[2];_tv=_tG;return null;}}})(_tt,_tu,_tv,_);if(_tw!=null){return _tw;}}},_tH=function(_tI,_tJ,_tK,_){while(1){var _tL=(function(_tM,_tN,_tO,_){var _tP=E(_tM);if(!_tP[0]){return [0,_47,_tO];}else{var _tQ=E(_tN);if(!_tQ[0]){return [0,_47,_tO];}else{var _tR=_tQ[1],_tS=new T(function(){var _tT=E(_tR);return B(_v(B(_H(0,B(_kf(imul(E(_tT[10]),100)|0,E(_tT[9]))),_11)),_kk));}),_tU=B(A(_kq,[_4d,_sN,_tP[1],_kl,_tS,_tO,_])),_tV=_tU,_tW=new T(function(){return E(E(_tV)[2]);});_tI=_tP[2];_tJ=_tQ[2];_tK=_tW;return null;}}})(_tI,_tJ,_tK,_);if(_tL!=null){return _tL;}}},_tX=function(_tY){return new F(function(){return _mW("Main.hs:94:55-65|lambda");});},_tZ=new T(function(){return B(_tX(_));}),_u0=function(_u1,_u2,_u3,_){var _u4=jsQuerySelectorAll(_u1,toJSStr(_lD));if(!_u4[0]){return E(_tZ);}else{var _u5=_u4[1];if(!E(_u4[2])[0]){var _u6=new T(function(){return E(E(_u2)[1]);}),_u7=function(_u8,_u9,_ua,_){var _ub=jsQuerySelectorAll(E(_u5),toJSStr(E(_u8))),_uc=_ub,_ud=_u6,_ue=_ua,_=_;while(1){var _uf=(function(_ug,_uh,_ui,_){var _uj=E(_ug);if(!_uj[0]){return [0,_47,_ui];}else{var _uk=E(_uh);if(!_uk[0]){return [0,_47,_ui];}else{var _ul=_uk[1],_um=new T(function(){return B(A(_u9,[_ul]));}),_un=B(A(_l3,[_4d,_sN,_uj[1],_l2,_um,_ui,_])),_uo=_un,_up=new T(function(){return E(E(_uo)[2]);});_uc=_uj[2];_ud=_uk[2];_ue=_up;return null;}}})(_uc,_ud,_ue,_);if(_uf!=null){return _uf;}}},_uq=B(_u7(_lV,_lT,_u3,_)),_ur=_uq,_us=new T(function(){return E(E(_ur)[2]);}),_ut=B(_u7(_lS,_lQ,_us,_)),_uu=_ut,_uv=new T(function(){return E(E(_uu)[2]);}),_uw=B(_u7(_lP,_lN,_uv,_)),_ux=_uw,_uy=E(_u5),_uz=jsQuerySelectorAll(_uy,toJSStr(E(_lM))),_uA=new T(function(){return E(E(_ux)[2]);}),_uB=B(_sP(_uz,_u6,_uA,_)),_uC=_uB,_uD=new T(function(){return E(E(_uC)[2]);}),_uE=B(_u7(_lL,_lJ,_uD,_)),_uF=_uE,_uG=new T(function(){return E(E(_uF)[2]);}),_uH=B(_u7(_lI,_lG,_uG,_)),_uI=_uH,_uJ=jsQuerySelectorAll(_uy,toJSStr(E(_lF))),_uK=new T(function(){return E(E(_uI)[2]);}),_uL=B(_t5(_uJ,_u6,_uK,_)),_uM=_uL,_uN=jsQuerySelectorAll(_u1,toJSStr(_lB));if(!_uN[0]){return E(_tZ);}else{if(!E(_uN[2])[0]){var _uO=E(_uN[1]),_uP=jsQuerySelectorAll(_uO,toJSStr(E(_ly))),_uQ=new T(function(){return E(E(_uM)[2]);}),_uR=new T(function(){return E(E(_u2)[2]);},1),_uS=B(_ts(_uP,_uR,_uQ,_)),_uT=_uS,_uU=jsQuerySelectorAll(_uO,toJSStr(E(_lE))),_uV=new T(function(){return E(E(_uT)[2]);}),_uW=new T(function(){return E(E(_u2)[2]);},1);return new F(function(){return _tH(_uU,_uW,_uV,_);});}else{return E(_tZ);}}}else{return E(_tZ);}}},_uX=function(_uY,_uZ,_v0,_){var _v1=B(A(_nR,[_4d,_sN,_uY,_l2,_v0,_])),_v2=_v1,_v3=new T(function(){return E(E(_v2)[2]);}),_v4=new T(function(){return B(_v(E(_v2)[1],_uZ));});return new F(function(){return A(_l3,[_4d,_sN,_uY,_l2,_v4,_v3,_]);});},_v5=function(_v6,_v7,_v8,_){var _v9=rMV(_v7),_va=E(_v6),_vb=jsQuerySelectorAll(_va,toJSStr(_lD));if(!_vb[0]){return E(_tZ);}else{var _vc=_vb[1];if(!E(_vb[2])[0]){var _vd=B(A(_l3,[_4d,_sN,_vc,_l2,_11,_v8,_])),_ve=_vd,_vf=E(E(_v9)[7]),_vg=function(_vh,_vi,_){while(1){var _vj=(function(_vk,_vl,_){var _vm=E(_vk);if(!_vm[0]){return [0,_47,_vl];}else{var _vn=B(_uX(_vc,_p1,_vl,_)),_vo=_vn,_vp=new T(function(){return E(E(_vo)[2]);});_vh=_vm[2];_vi=_vp;return null;}})(_vh,_vi,_);if(_vj!=null){return _vj;}}},_vq=new T(function(){return E(E(_ve)[2]);}),_vr=B(_vg(_vf[1],_vq,_)),_vs=_vr,_vt=jsQuerySelectorAll(_va,toJSStr(_lB));if(!_vt[0]){return E(_tZ);}else{var _vu=_vt[1];if(!E(_vt[2])[0]){var _vv=new T(function(){return E(E(_vs)[2]);}),_vw=B(A(_l3,[_4d,_sN,_vu,_l2,_11,_vv,_])),_vx=_vw,_vy=function(_vz,_vA,_){while(1){var _vB=(function(_vC,_vD,_){var _vE=E(_vC);if(!_vE[0]){return [0,_47,_vD];}else{var _vF=B(_uX(_vu,_oB,_vD,_)),_vG=_vF,_vH=new T(function(){return E(E(_vG)[2]);});_vz=_vE[2];_vA=_vH;return null;}})(_vz,_vA,_);if(_vB!=null){return _vB;}}},_vI=new T(function(){return E(E(_vx)[2]);}),_vJ=B(_vy(_vf[2],_vI,_)),_vK=_vJ,_vL=new T(function(){return E(E(_vK)[2]);});return new F(function(){return _u0(_va,_vf,_vL,_);});}else{return E(_tZ);}}}else{return E(_tZ);}}},_vM=function(_vN,_vO,_vP){while(1){var _vQ=E(_vP);if(!_vQ[0]){var _vR=_vQ[4],_vS=_vQ[5],_vT=E(_vQ[2]),_vU=E(_vT[1]);if(_vN>=_vU){if(_vN!=_vU){_vP=_vS;continue;}else{var _vV=E(_vO),_vW=E(_vT[2]);if(_vV>=_vW){if(_vV!=_vW){_vO=_vV;_vP=_vS;continue;}else{return E(_vQ[3]);}}else{_vO=_vV;_vP=_vR;continue;}}}else{_vP=_vR;continue;}}else{return E(_qN);}}},_vX=new T(function(){return B(unCStr("&nbsp;"));}),_vY=new T(function(){return B(unCStr("@"));}),_vZ=new T(function(){return B(_v(_vX,_vY));}),_w0=function(_w1){var _w2=E(_w1);if(_w2==1){return E(_vZ);}else{var _w3=new T(function(){return B(_w0(_w2-1|0));},1);return new F(function(){return _v(_vX,_w3);});}},_w4=0,_w5="dungeon-field",_w6="dungeon-battle",_w7=function(_w8,_){while(1){var _w9=E(_w8);if(!_w9[0]){return _47;}else{var _wa=B(A(_l3,[_4d,_4S,_w9[1],_l2,_11,_]));_w8=_w9[2];continue;}}},_wb=function(_wc,_){while(1){var _wd=E(_wc);if(!_wd[0]){return _47;}else{var _we=B(A(_l3,[_4d,_4S,_wd[1],_l2,_11,_]));_wc=_wd[2];continue;}}},_wf=0,_wg=new T(function(){return document;}),_wh=function(){ $('#tabs a[href="#dungeon"]').tab('show'); },_wi=function(){ $('#tabs a[href="#dungeon-battle"]').tab('show'); },_wj=(function(e){return e.parentNode;}),_wk=function(_wl){while(1){var _wm=E(_wl);if(!_wm[0]){return true;}else{if(E(_wm[1])>0){return false;}else{_wl=_wm[2];continue;}}}},_wn=new T(function(){return B(unCStr("<br>"));}),_wo=function(_wp,_wq){if(_wp<=_wq){var _wr=function(_ws){var _wt=new T(function(){if(_ws!=_wq){return B(_wr(_ws+1|0));}else{return [0];}});return [1,_ws,_wt];};return new F(function(){return _wr(_wp);});}else{return [0];}},_wu=new T(function(){return B(_wo(0,34));}),_wv=new T(function(){return B(_wo(0,44));}),_ww=function(_wx){var _wy=E(_wx);if(!_wy[0]){return [0];}else{var _wz=_wy[2],_wA=E(_wy[1]);if(E(_wA)==32){var _wB=new T(function(){return B(_ww(_wz));},1);return new F(function(){return _v(_vX,_wB);});}else{var _wC=new T(function(){return B(_ww(_wz));},1);return new F(function(){return _v([1,_wA,_11],_wC);});}}},_wD=function(_wE){var _wF=E(_wE);if(!_wF[0]){return [0];}else{var _wG=_wF[2],_wH=new T(function(){return B(_wD(_wG));},1);return new F(function(){return _v(_wF[1],_wH);});}},_wI=function(_wJ,_wK){var _wL=E(_wK);if(!_wL[0]){return [0];}else{var _wM=_wL[1],_wN=_wL[2],_wO=new T(function(){return B(_wI(_wJ,_wN));}),_wP=new T(function(){return B(A(_wJ,[_wM]));});return [1,_wP,_wO];}},_wQ=function(_wR,_wS){var _wT=E(_wS);if(!_wT[0]){return [0];}else{var _wU=_wT[2],_wV=new T(function(){return B(_wQ(_wR,_wU));});return [1,_wR,[1,_wT[1],_wV]];}},_wW=function(_wX){var _wY=function(_wZ){var _x0=function(_x1,_x2){var _x3=E(_x1);if(!_x3[0]){return [0];}else{var _x4=_x3[1],_x5=_x3[2],_x6=E(_x2);if(_x6==1){var _x7=new T(function(){return B(_vM(E(_x4),_wZ,_wX));});return [1,_x7,_11];}else{var _x8=new T(function(){return B(_x0(_x5,_x6-1|0));}),_x9=new T(function(){return B(_vM(E(_x4),_wZ,_wX));});return [1,_x9,_x8];}}};return new F(function(){return _x0(_wv,45);});},_xa=B(_wI(_wY,_wu));if(!_xa[0]){return [0];}else{var _xb=_xa[2],_xc=new T(function(){return B(_wQ(_wn,_xb));});return new F(function(){return _ww(B(_wD([1,_xa[1],_xc])));});}},_xd=function(_xe){return E(E(_xe)[2]);},_xf=function(_xg,_xh,_xi,_xj){var _xk=E(_xh),_xl=E(_xj);if(!_xl[0]){var _xm=_xl[2],_xn=_xl[3],_xo=_xl[4],_xp=_xl[5];switch(B(A(_xd,[_xg,_xk,_xm]))){case 0:return new F(function(){return _6z(_xm,_xn,B(_xf(_xg,_xk,_xi,_xo)),_xp);});break;case 1:return [0,_xl[1],E(_xk),_xi,E(_xo),E(_xp)];default:return new F(function(){return _5G(_xm,_xn,_xo,B(_xf(_xg,_xk,_xi,_xp)));});}}else{return [0,1,E(_xk),_xi,E(_5B),E(_5B)];}},_xq=function(_xr,_xs,_xt,_xu){return new F(function(){return _xf(_xr,_xs,_xt,_xu);});},_xv=function(_xw,_xx,_xy){var _xz=function(_xA){var _xB=E(_xA);if(!_xB[0]){return E(_xy);}else{var _xC=E(_xB[1]);return new F(function(){return _xq(_xw,_xC[1],_xC[2],B(_xz(_xB[2])));});}};return new F(function(){return _xz(_xx);});},_xD=new T(function(){return B(unCStr("block"));}),_xE=[1,_11,_11],_xF=function(_xG){var _xH=E(_xG);if(!_xH[0]){return E(_xE);}else{var _xI=_xH[2],_xJ=new T(function(){return B(_xF(_xI));}),_xK=function(_xL){var _xM=E(_xL);if(!_xM[0]){return [0];}else{var _xN=_xM[1],_xO=_xM[2],_xP=new T(function(){return B(_xK(_xO));}),_xQ=function(_xR){var _xS=E(_xR);if(!_xS[0]){return E(_xP);}else{var _xT=_xS[2],_xU=new T(function(){return B(_xQ(_xT));});return [1,[1,_xN,_xS[1]],_xU];}};return new F(function(){return _xQ(_xJ);});}};return new F(function(){return _xK(_xH[1]);});}},_xV=function(_xW,_xX){if(0>=_xW){return E(_xE);}else{var _xY=[1,_xX,_11],_xZ=function(_y0){var _y1=E(_y0);if(_y1==1){return E(_xY);}else{var _y2=new T(function(){return B(_xZ(_y1-1|0));});return [1,_xX,_y2];}};return new F(function(){return _xF(B(_xZ(_xW)));});}},_y3=2,_y4=[1,_y3,_11],_y5=1,_y6=[1,_y5,_y4],_y7=[1,_wf,_y6],_y8=-1,_y9=[1,_y8,_y7],_ya=-2,_yb=[1,_ya,_y9],_yc=new T(function(){return B(_xV(2,_yb));}),_yd=function(_ye){return new F(function(){return _mW("Main.hs:(410,64)-(412,35)|lambda");});},_yf=new T(function(){return B(_yd(_));}),_yg=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:398:3-9"));}),_yh=[0,_3c,_3d,_11,_yg,_3c,_3c],_yi=new T(function(){return B(_3a(_yh));}),_yj=new T(function(){return B(unCStr("#tabs a[href=\"#dungeon-battle\"]"));}),_yk=new T(function(){return B(unCStr("step-battle"));}),_yl=[1,_lA,_yk],_ym=new T(function(){return B(unCStr("player"));}),_yn=new T(function(){return B(unCStr("none"));}),_yo=new T(function(){return B(unCStr("display"));}),_yp=new T(function(){return B(unCStr("#enemy-chara"));}),_yq=new T(function(){return B(unCStr("#player-chara"));}),_yr=function(_ys){return E(E(_ys)[10]);},_yt=function(_yu){return E(E(_yu)[1]);},_yv=function(_yw){return E(E(_yw)[2]);},_yx=function(_yy){return E(E(_yy)[1]);},_yz=function(_){return new F(function(){return nMV(_3c);});},_yA=new T(function(){return B(_3v(_yz));}),_yB=(function(e,name,f){e.addEventListener(name,f,false);return [f];}),_yC=function(_yD){return E(E(_yD)[2]);},_yE=function(_yF,_yG,_yH,_yI,_yJ,_yK){var _yL=B(_yt(_yF)),_yM=B(_nD(_yL)),_yN=new T(function(){return B(_ko(_yL));}),_yO=new T(function(){return B(_nP(_yM));}),_yP=new T(function(){return B(A(_km,[_yG,_yI]));}),_yQ=new T(function(){return B(A(_yx,[_yH,_yJ]));}),_yR=function(_yS){return new F(function(){return A(_yO,[[0,_yQ,_yP,_yS]]);});},_yT=function(_yU){var _yV=new T(function(){var _yW=new T(function(){var _yX=E(_yP),_yY=E(_yQ),_yZ=E(_yU),_z0=function(_z1,_){var _z2=B(A(_yZ,[_z1,_]));return _3z;},_z3=__createJSFunc(2,E(_z0)),_z4=_z3,_z5=function(_){return new F(function(){return E(_yB)(_yX,_yY,_z4);});};return E(_z5);});return B(A(_yN,[_yW]));});return new F(function(){return A(_nF,[_yM,_yV,_yR]);});},_z6=new T(function(){var _z7=new T(function(){return B(_ko(_yL));}),_z8=function(_z9){var _za=new T(function(){var _zb=function(_){var _=wMV(E(_yA),[1,_z9]);return new F(function(){return A(_yv,[_yH,_yJ,_z9,_]);});};return B(A(_z7,[_zb]));});return new F(function(){return A(_nF,[_yM,_za,_yK]);});};return B(A(_yC,[_yF,_z8]));});return new F(function(){return A(_nF,[_yM,_z6,_yT]);});},_zc=new T(function(){return B(unCStr(" found!"));}),_zd=function(_ze){var _zf=new T(function(){return B(_v(fromJSStr(E(_ze)),_zc));});return new F(function(){return err(B(unAppCStr("No element with ID ",_zf)));});},_zg=function(_zh,_zi,_zj,_zk,_zl,_zm,_zn,_){var _zo=E(_zj),_zp=_zo[1],_zq=_zo[2],_zr=function(_,_zs,_zt,_zu,_zv,_zw,_zx,_zy,_zz){var _zA=function(_,_zB,_zC,_zD,_zE,_zF,_zG,_zH,_zI){var _zJ=function(_,_zK,_zL,_zM,_zN,_zO,_zP,_zQ,_zR){var _zS=function(_,_zT,_zU,_zV,_zW,_zX,_zY,_zZ,_A0){var _A1=jsFind(toJSStr(E(_ym)));if(!_A1[0]){return new F(function(){return die(_yi);});}else{var _A2=new T(function(){var _A3=function(_A4){while(1){var _A5=(function(_A6){var _A7=E(_A6);if(!_A7[0]){return [0];}else{var _A8=_A7[2],_A9=E(_A7[1]);if(!_A9[0]){_A4=_A8;return null;}else{var _Aa=E(_A9[2]);if(!_Aa[0]){_A4=_A8;return null;}else{if(!E(_Aa[2])[0]){var _Ab=E(_zU),_Ac=E(_A9[1]);if(0>(_Ab+_Ac|0)){var _Ad=function(_Ae){while(1){var _Af=(function(_Ag){var _Ah=E(_Ag);if(!_Ah[0]){return [0];}else{var _Ai=_Ah[2],_Aj=E(_Ah[1]);if(!_Aj[0]){_Ae=_Ai;return null;}else{var _Ak=E(_Aj[2]);if(!_Ak[0]){_Ae=_Ai;return null;}else{if(!E(_Ak[2])[0]){var _Al=E(_Aj[1]);if(0>(_Ab+_Al|0)){_Ae=_Ai;return null;}else{if((_Ab+_Al|0)>44){_Ae=_Ai;return null;}else{var _Am=E(_zV),_An=E(_Ak[1]);if(0>(_Am+_An|0)){_Ae=_Ai;return null;}else{if((_Am+_An|0)>34){_Ae=_Ai;return null;}else{var _Ao=new T(function(){return B(_Ad(_Ai));}),_Ap=_Ab+_Al|0,_Aq=_Am+_An|0,_Ar=new T(function(){return B(_qO(_Ap,_Aq,_zX));});return [1,[0,[0,_Ap,_Aq],_Ar],_Ao];}}}}}else{_Ae=_Ai;return null;}}}}})(_Ae);if(_Af!=null){return _Af;}}};return new F(function(){return _Ad(_A8);});}else{if((_Ab+_Ac|0)>44){var _As=function(_At){while(1){var _Au=(function(_Av){var _Aw=E(_Av);if(!_Aw[0]){return [0];}else{var _Ax=_Aw[2],_Ay=E(_Aw[1]);if(!_Ay[0]){_At=_Ax;return null;}else{var _Az=E(_Ay[2]);if(!_Az[0]){_At=_Ax;return null;}else{if(!E(_Az[2])[0]){var _AA=E(_Ay[1]);if(0>(_Ab+_AA|0)){_At=_Ax;return null;}else{if((_Ab+_AA|0)>44){_At=_Ax;return null;}else{var _AB=E(_zV),_AC=E(_Az[1]);if(0>(_AB+_AC|0)){_At=_Ax;return null;}else{if((_AB+_AC|0)>34){_At=_Ax;return null;}else{var _AD=new T(function(){return B(_As(_Ax));}),_AE=_Ab+_AA|0,_AF=_AB+_AC|0,_AG=new T(function(){return B(_qO(_AE,_AF,_zX));});return [1,[0,[0,_AE,_AF],_AG],_AD];}}}}}else{_At=_Ax;return null;}}}}})(_At);if(_Au!=null){return _Au;}}};return new F(function(){return _As(_A8);});}else{var _AH=E(_zV),_AI=E(_Aa[1]);if(0>(_AH+_AI|0)){var _AJ=function(_AK){while(1){var _AL=(function(_AM){var _AN=E(_AM);if(!_AN[0]){return [0];}else{var _AO=_AN[2],_AP=E(_AN[1]);if(!_AP[0]){_AK=_AO;return null;}else{var _AQ=E(_AP[2]);if(!_AQ[0]){_AK=_AO;return null;}else{if(!E(_AQ[2])[0]){var _AR=E(_AP[1]);if(0>(_Ab+_AR|0)){_AK=_AO;return null;}else{if((_Ab+_AR|0)>44){_AK=_AO;return null;}else{var _AS=E(_AQ[1]);if(0>(_AH+_AS|0)){_AK=_AO;return null;}else{if((_AH+_AS|0)>34){_AK=_AO;return null;}else{var _AT=new T(function(){return B(_AJ(_AO));}),_AU=_Ab+_AR|0,_AV=_AH+_AS|0,_AW=new T(function(){return B(_qO(_AU,_AV,_zX));});return [1,[0,[0,_AU,_AV],_AW],_AT];}}}}}else{_AK=_AO;return null;}}}}})(_AK);if(_AL!=null){return _AL;}}};return new F(function(){return _AJ(_A8);});}else{if((_AH+_AI|0)>34){var _AX=function(_AY){while(1){var _AZ=(function(_B0){var _B1=E(_B0);if(!_B1[0]){return [0];}else{var _B2=_B1[2],_B3=E(_B1[1]);if(!_B3[0]){_AY=_B2;return null;}else{var _B4=E(_B3[2]);if(!_B4[0]){_AY=_B2;return null;}else{if(!E(_B4[2])[0]){var _B5=E(_B3[1]);if(0>(_Ab+_B5|0)){_AY=_B2;return null;}else{if((_Ab+_B5|0)>44){_AY=_B2;return null;}else{var _B6=E(_B4[1]);if(0>(_AH+_B6|0)){_AY=_B2;return null;}else{if((_AH+_B6|0)>34){_AY=_B2;return null;}else{var _B7=new T(function(){return B(_AX(_B2));}),_B8=_Ab+_B5|0,_B9=_AH+_B6|0,_Ba=new T(function(){return B(_qO(_B8,_B9,_zX));});return [1,[0,[0,_B8,_B9],_Ba],_B7];}}}}}else{_AY=_B2;return null;}}}}})(_AY);if(_AZ!=null){return _AZ;}}};return new F(function(){return _AX(_A8);});}else{var _Bb=new T(function(){var _Bc=function(_Bd){while(1){var _Be=(function(_Bf){var _Bg=E(_Bf);if(!_Bg[0]){return [0];}else{var _Bh=_Bg[2],_Bi=E(_Bg[1]);if(!_Bi[0]){_Bd=_Bh;return null;}else{var _Bj=E(_Bi[2]);if(!_Bj[0]){_Bd=_Bh;return null;}else{if(!E(_Bj[2])[0]){var _Bk=E(_Bi[1]);if(0>(_Ab+_Bk|0)){_Bd=_Bh;return null;}else{if((_Ab+_Bk|0)>44){_Bd=_Bh;return null;}else{var _Bl=E(_Bj[1]);if(0>(_AH+_Bl|0)){_Bd=_Bh;return null;}else{if((_AH+_Bl|0)>34){_Bd=_Bh;return null;}else{var _Bm=new T(function(){return B(_Bc(_Bh));}),_Bn=_Ab+_Bk|0,_Bo=_AH+_Bl|0,_Bp=new T(function(){return B(_qO(_Bn,_Bo,_zX));});return [1,[0,[0,_Bn,_Bo],_Bp],_Bm];}}}}}else{_Bd=_Bh;return null;}}}}})(_Bd);if(_Be!=null){return _Be;}}};return B(_Bc(_A8));}),_Bq=_Ab+_Ac|0,_Br=_AH+_AI|0,_Bs=new T(function(){return B(_qO(_Bq,_Br,_zX));});return [1,[0,[0,_Bq,_Br],_Bs],_Bb];}}}}}else{_A4=_A8;return null;}}}}})(_A4);if(_A5!=null){return _A5;}}};return B(_xv(_qL,B(_A3(_yc)),_zY));}),_Bt=new T(function(){var _Bu=E(_zV);if(0>=_Bu){var _Bv=E(_zU);if(0>=_Bv){return E(_vY);}else{return B(_w0(_Bv));}}else{var _Bw=new T(function(){var _Bx=new T(function(){var _By=E(_zU);if(0>=_By){return E(_vY);}else{return B(_w0(_By));}},1);return B(_v(_wn,_Bx));}),_Bz=function(_BA){var _BB=E(_BA);if(_BB==1){return E(_Bw);}else{var _BC=new T(function(){return B(_Bz(_BB-1|0));},1);return new F(function(){return _v(_wn,_BC);});}};return B(_Bz(_Bu));}}),_BD=B(A(_l3,[_4d,_sN,_A1[1],_l2,_Bt,[0,_zT,[0,_zU,_zV],_zW,_zX,_A2,_zZ,_A0],_])),_BE=_BD,_BF=E(_w5),_BG=jsFind(_BF);if(!_BG[0]){return new F(function(){return _zd(_BF);});}else{var _BH=new T(function(){return E(E(_BE)[2]);}),_BI=new T(function(){var _BJ=new T(function(){return E(E(_BH)[5]);});return B(_wW(_BJ));}),_BK=B(A(_l3,[_4d,_sN,_BG[1],_l2,_BI,_BH,_])),_BL=E(E(_BK)[2]);if(E(_BL[6])==5){var _BM=E(_3z),_BN=E(_wi)(_BM),_BO=E(_wg),_BP=toJSStr(E(_yj)),_BQ=jsQuerySelectorAll(_BO,_BP);if(!_BQ[0]){return E(_yf);}else{if(!E(_BQ[2])[0]){var _BR=E(_wj),_BS=_BR(E(_BQ[1])),_BT=B(A(_kq,[_4d,_sN,_BS,_yo,_xD,[0,_BL[1],_BL[2],_BL[3],_BL[4],_BL[5],_wf,_BL[7]],_])),_BU=_BT,_BV=E(_w6),_BW=jsFind(_BV);if(!_BW[0]){return new F(function(){return _zd(_BV);});}else{var _BX=_BW[1],_BY=E(_zh),_BZ=new T(function(){return E(E(_BU)[2]);}),_C0=B(_v5(_BX,_BY,_BZ,_)),_C1=_C0,_C2=E(_BX),_C3=jsQuerySelectorAll(_C2,toJSStr(_yl));if(!_C3[0]){return E(_tZ);}else{var _C4=_C3[1];if(!E(_C3[2])[0]){var _C5=function(_C6,_){var _C7=rMV(_BY),_C8=E(_C7),_C9=E(_C8[7]),_Ca=B(_iY(_C9[1],_C9[2],_C9[3],_C9[4],_C9[5],_)),_=wMV(_BY,[0,_C8[1],_C8[2],_C8[3],_C8[4],_C8[5],_C8[6],E(_Ca)[2]]),_Cb=rMV(_BY);if(!B(_wk(B(_wI(_yr,E(E(_Cb)[7])[2]))))){var _Cc=rMV(_BY),_Cd=_Cc,_Ce=new T(function(){return E(E(_Cd)[7]);});return new F(function(){return _n2(_C2,_Ce,_);});}else{var _Cf=E(_wh)(_BM),_Cg=jsQuerySelectorAll(_BO,_BP);if(!_Cg[0]){return new F(function(){return _sO(_);});}else{if(!E(_Cg[2])[0]){var _Ch=_BR(E(_Cg[1])),_Ci=B(A(_kq,[_4d,_4S,_Ch,_yo,_yn,_])),_Cj=E(_C4),_Ck=jsQuerySelectorAll(_Cj,toJSStr(E(_yq))),_Cl=B(_w7(_Ck,_)),_Cm=jsQuerySelectorAll(_Cj,toJSStr(E(_yp))),_Cn=B(_wb(_Cm,_)),_Co=rMV(_BY),_Cp=_Co,_Cq=new T(function(){return E(E(_Cp)[7]);});return new F(function(){return _n2(_C2,_Cq,_);});}else{return new F(function(){return _sO(_);});}}}},_Cr=B(A(_yE,[_4T,_4d,_46,_C4,_w4,_C5,_])),_Cs=new T(function(){return E(E(_C1)[2]);});return [0,_47,_Cs];}else{return E(_tZ);}}}}else{return E(_yf);}}}else{return [0,_47,_BL];}}}};if(!B(_es(_zi,39))){return new F(function(){return _zS(_,_zK,_zL,_zM,_zN,_zO,_zP,_zQ,_zR);});}else{var _Ct=E(_zL),_Cu=_Ct+1|0;switch(E(B(_vM(_Cu,_zM,_zO)))){case 35:var _Cv=new T(function(){return E(_zQ)+1|0;});return new F(function(){return _zS(_,_zK,_Cu,_zM,_zN,_zO,_zP,_Cv,_zR);});break;case 45:var _Cw=new T(function(){return E(_zQ)+1|0;});return new F(function(){return _zS(_,_zK,_Cu,_zM,_zN,_zO,_zP,_Cw,_zR);});break;default:return new F(function(){return _zS(_,_zK,_Ct,_zM,_zN,_zO,_zP,_zQ,_zR);});}}};if(!B(_es(_zi,37))){return new F(function(){return _zJ(_,_zB,_zC,_zD,_zE,_zF,_zG,_zH,_zI);});}else{var _Cx=_zC+(-1)|0;switch(E(B(_vM(_Cx,_zD,_zF)))){case 35:var _Cy=new T(function(){return E(_zH)+1|0;});return new F(function(){return _zJ(_,_zB,_Cx,_zD,_zE,_zF,_zG,_Cy,_zI);});break;case 45:var _Cz=new T(function(){return E(_zH)+1|0;});return new F(function(){return _zJ(_,_zB,_Cx,_zD,_zE,_zF,_zG,_Cz,_zI);});break;default:return new F(function(){return _zJ(_,_zB,_zC,_zD,_zE,_zF,_zG,_zH,_zI);});}}};if(!B(_es(_zi,40))){return new F(function(){return _zA(_,_zs,_zt,_zu,_zv,_zw,_zx,_zy,_zz);});}else{var _CA=new T(function(){return E(_zu)+1|0;});switch(E(B(_vM(_zt,_CA,_zw)))){case 35:var _CB=new T(function(){return E(_zy)+1|0;});return new F(function(){return _zA(_,_zs,_zt,_CA,_zv,_zw,_zx,_CB,_zz);});break;case 45:var _CC=new T(function(){return E(_zy)+1|0;});return new F(function(){return _zA(_,_zs,_zt,_CA,_zv,_zw,_zx,_CC,_zz);});break;default:return new F(function(){return _zA(_,_zs,_zt,_zu,_zv,_zw,_zx,_zy,_zz);});}}};if(!B(_es(_zi,38))){var _CD=function(_,_CE,_CF,_CG,_CH,_CI,_CJ,_CK,_CL){var _CM=function(_,_CN,_CO,_CP,_CQ,_CR,_CS,_CT,_CU){var _CV=function(_,_CW,_CX,_CY,_CZ,_D0,_D1,_D2,_D3){var _D4=jsFind(toJSStr(E(_ym)));if(!_D4[0]){return new F(function(){return die(_yi);});}else{var _D5=new T(function(){var _D6=function(_D7){while(1){var _D8=(function(_D9){var _Da=E(_D9);if(!_Da[0]){return [0];}else{var _Db=_Da[2],_Dc=E(_Da[1]);if(!_Dc[0]){_D7=_Db;return null;}else{var _Dd=E(_Dc[2]);if(!_Dd[0]){_D7=_Db;return null;}else{if(!E(_Dd[2])[0]){var _De=E(_CX),_Df=E(_Dc[1]);if(0>(_De+_Df|0)){var _Dg=function(_Dh){while(1){var _Di=(function(_Dj){var _Dk=E(_Dj);if(!_Dk[0]){return [0];}else{var _Dl=_Dk[2],_Dm=E(_Dk[1]);if(!_Dm[0]){_Dh=_Dl;return null;}else{var _Dn=E(_Dm[2]);if(!_Dn[0]){_Dh=_Dl;return null;}else{if(!E(_Dn[2])[0]){var _Do=E(_Dm[1]);if(0>(_De+_Do|0)){_Dh=_Dl;return null;}else{if((_De+_Do|0)>44){_Dh=_Dl;return null;}else{var _Dp=E(_CY),_Dq=E(_Dn[1]);if(0>(_Dp+_Dq|0)){_Dh=_Dl;return null;}else{if((_Dp+_Dq|0)>34){_Dh=_Dl;return null;}else{var _Dr=new T(function(){return B(_Dg(_Dl));}),_Ds=_De+_Do|0,_Dt=_Dp+_Dq|0,_Du=new T(function(){return B(_qO(_Ds,_Dt,_D0));});return [1,[0,[0,_Ds,_Dt],_Du],_Dr];}}}}}else{_Dh=_Dl;return null;}}}}})(_Dh);if(_Di!=null){return _Di;}}};return new F(function(){return _Dg(_Db);});}else{if((_De+_Df|0)>44){var _Dv=function(_Dw){while(1){var _Dx=(function(_Dy){var _Dz=E(_Dy);if(!_Dz[0]){return [0];}else{var _DA=_Dz[2],_DB=E(_Dz[1]);if(!_DB[0]){_Dw=_DA;return null;}else{var _DC=E(_DB[2]);if(!_DC[0]){_Dw=_DA;return null;}else{if(!E(_DC[2])[0]){var _DD=E(_DB[1]);if(0>(_De+_DD|0)){_Dw=_DA;return null;}else{if((_De+_DD|0)>44){_Dw=_DA;return null;}else{var _DE=E(_CY),_DF=E(_DC[1]);if(0>(_DE+_DF|0)){_Dw=_DA;return null;}else{if((_DE+_DF|0)>34){_Dw=_DA;return null;}else{var _DG=new T(function(){return B(_Dv(_DA));}),_DH=_De+_DD|0,_DI=_DE+_DF|0,_DJ=new T(function(){return B(_qO(_DH,_DI,_D0));});return [1,[0,[0,_DH,_DI],_DJ],_DG];}}}}}else{_Dw=_DA;return null;}}}}})(_Dw);if(_Dx!=null){return _Dx;}}};return new F(function(){return _Dv(_Db);});}else{var _DK=E(_CY),_DL=E(_Dd[1]);if(0>(_DK+_DL|0)){var _DM=function(_DN){while(1){var _DO=(function(_DP){var _DQ=E(_DP);if(!_DQ[0]){return [0];}else{var _DR=_DQ[2],_DS=E(_DQ[1]);if(!_DS[0]){_DN=_DR;return null;}else{var _DT=E(_DS[2]);if(!_DT[0]){_DN=_DR;return null;}else{if(!E(_DT[2])[0]){var _DU=E(_DS[1]);if(0>(_De+_DU|0)){_DN=_DR;return null;}else{if((_De+_DU|0)>44){_DN=_DR;return null;}else{var _DV=E(_DT[1]);if(0>(_DK+_DV|0)){_DN=_DR;return null;}else{if((_DK+_DV|0)>34){_DN=_DR;return null;}else{var _DW=new T(function(){return B(_DM(_DR));}),_DX=_De+_DU|0,_DY=_DK+_DV|0,_DZ=new T(function(){return B(_qO(_DX,_DY,_D0));});return [1,[0,[0,_DX,_DY],_DZ],_DW];}}}}}else{_DN=_DR;return null;}}}}})(_DN);if(_DO!=null){return _DO;}}};return new F(function(){return _DM(_Db);});}else{if((_DK+_DL|0)>34){var _E0=function(_E1){while(1){var _E2=(function(_E3){var _E4=E(_E3);if(!_E4[0]){return [0];}else{var _E5=_E4[2],_E6=E(_E4[1]);if(!_E6[0]){_E1=_E5;return null;}else{var _E7=E(_E6[2]);if(!_E7[0]){_E1=_E5;return null;}else{if(!E(_E7[2])[0]){var _E8=E(_E6[1]);if(0>(_De+_E8|0)){_E1=_E5;return null;}else{if((_De+_E8|0)>44){_E1=_E5;return null;}else{var _E9=E(_E7[1]);if(0>(_DK+_E9|0)){_E1=_E5;return null;}else{if((_DK+_E9|0)>34){_E1=_E5;return null;}else{var _Ea=new T(function(){return B(_E0(_E5));}),_Eb=_De+_E8|0,_Ec=_DK+_E9|0,_Ed=new T(function(){return B(_qO(_Eb,_Ec,_D0));});return [1,[0,[0,_Eb,_Ec],_Ed],_Ea];}}}}}else{_E1=_E5;return null;}}}}})(_E1);if(_E2!=null){return _E2;}}};return new F(function(){return _E0(_Db);});}else{var _Ee=new T(function(){var _Ef=function(_Eg){while(1){var _Eh=(function(_Ei){var _Ej=E(_Ei);if(!_Ej[0]){return [0];}else{var _Ek=_Ej[2],_El=E(_Ej[1]);if(!_El[0]){_Eg=_Ek;return null;}else{var _Em=E(_El[2]);if(!_Em[0]){_Eg=_Ek;return null;}else{if(!E(_Em[2])[0]){var _En=E(_El[1]);if(0>(_De+_En|0)){_Eg=_Ek;return null;}else{if((_De+_En|0)>44){_Eg=_Ek;return null;}else{var _Eo=E(_Em[1]);if(0>(_DK+_Eo|0)){_Eg=_Ek;return null;}else{if((_DK+_Eo|0)>34){_Eg=_Ek;return null;}else{var _Ep=new T(function(){return B(_Ef(_Ek));}),_Eq=_De+_En|0,_Er=_DK+_Eo|0,_Es=new T(function(){return B(_qO(_Eq,_Er,_D0));});return [1,[0,[0,_Eq,_Er],_Es],_Ep];}}}}}else{_Eg=_Ek;return null;}}}}})(_Eg);if(_Eh!=null){return _Eh;}}};return B(_Ef(_Db));}),_Et=_De+_Df|0,_Eu=_DK+_DL|0,_Ev=new T(function(){return B(_qO(_Et,_Eu,_D0));});return [1,[0,[0,_Et,_Eu],_Ev],_Ee];}}}}}else{_D7=_Db;return null;}}}}})(_D7);if(_D8!=null){return _D8;}}};return B(_xv(_qL,B(_D6(_yc)),_D1));}),_Ew=new T(function(){var _Ex=E(_CY);if(0>=_Ex){var _Ey=E(_CX);if(0>=_Ey){return E(_vY);}else{return B(_w0(_Ey));}}else{var _Ez=new T(function(){var _EA=new T(function(){var _EB=E(_CX);if(0>=_EB){return E(_vY);}else{return B(_w0(_EB));}},1);return B(_v(_wn,_EA));}),_EC=function(_ED){var _EE=E(_ED);if(_EE==1){return E(_Ez);}else{var _EF=new T(function(){return B(_EC(_EE-1|0));},1);return new F(function(){return _v(_wn,_EF);});}};return B(_EC(_Ex));}}),_EG=B(A(_l3,[_4d,_sN,_D4[1],_l2,_Ew,[0,_CW,[0,_CX,_CY],_CZ,_D0,_D5,_D2,_D3],_])),_EH=_EG,_EI=E(_w5),_EJ=jsFind(_EI);if(!_EJ[0]){return new F(function(){return _zd(_EI);});}else{var _EK=new T(function(){return E(E(_EH)[2]);}),_EL=new T(function(){var _EM=new T(function(){return E(E(_EK)[5]);});return B(_wW(_EM));}),_EN=B(A(_l3,[_4d,_sN,_EJ[1],_l2,_EL,_EK,_])),_EO=E(E(_EN)[2]);if(E(_EO[6])==5){var _EP=E(_3z),_EQ=E(_wi)(_EP),_ER=E(_wg),_ES=toJSStr(E(_yj)),_ET=jsQuerySelectorAll(_ER,_ES);if(!_ET[0]){return E(_yf);}else{if(!E(_ET[2])[0]){var _EU=E(_wj),_EV=_EU(E(_ET[1])),_EW=B(A(_kq,[_4d,_sN,_EV,_yo,_xD,[0,_EO[1],_EO[2],_EO[3],_EO[4],_EO[5],_wf,_EO[7]],_])),_EX=_EW,_EY=E(_w6),_EZ=jsFind(_EY);if(!_EZ[0]){return new F(function(){return _zd(_EY);});}else{var _F0=_EZ[1],_F1=E(_zh),_F2=new T(function(){return E(E(_EX)[2]);}),_F3=B(_v5(_F0,_F1,_F2,_)),_F4=_F3,_F5=E(_F0),_F6=jsQuerySelectorAll(_F5,toJSStr(_yl));if(!_F6[0]){return E(_tZ);}else{var _F7=_F6[1];if(!E(_F6[2])[0]){var _F8=function(_F9,_){var _Fa=rMV(_F1),_Fb=E(_Fa),_Fc=E(_Fb[7]),_Fd=B(_iY(_Fc[1],_Fc[2],_Fc[3],_Fc[4],_Fc[5],_)),_=wMV(_F1,[0,_Fb[1],_Fb[2],_Fb[3],_Fb[4],_Fb[5],_Fb[6],E(_Fd)[2]]),_Fe=rMV(_F1);if(!B(_wk(B(_wI(_yr,E(E(_Fe)[7])[2]))))){var _Ff=rMV(_F1),_Fg=_Ff,_Fh=new T(function(){return E(E(_Fg)[7]);});return new F(function(){return _n2(_F5,_Fh,_);});}else{var _Fi=E(_wh)(_EP),_Fj=jsQuerySelectorAll(_ER,_ES);if(!_Fj[0]){return new F(function(){return _sO(_);});}else{if(!E(_Fj[2])[0]){var _Fk=_EU(E(_Fj[1])),_Fl=B(A(_kq,[_4d,_4S,_Fk,_yo,_yn,_])),_Fm=E(_F7),_Fn=jsQuerySelectorAll(_Fm,toJSStr(E(_yq))),_Fo=B(_w7(_Fn,_)),_Fp=jsQuerySelectorAll(_Fm,toJSStr(E(_yp))),_Fq=B(_wb(_Fp,_)),_Fr=rMV(_F1),_Fs=_Fr,_Ft=new T(function(){return E(E(_Fs)[7]);});return new F(function(){return _n2(_F5,_Ft,_);});}else{return new F(function(){return _sO(_);});}}}},_Fu=B(A(_yE,[_4T,_4d,_46,_F7,_w4,_F8,_])),_Fv=new T(function(){return E(E(_F4)[2]);});return [0,_47,_Fv];}else{return E(_tZ);}}}}else{return E(_yf);}}}else{return [0,_47,_EO];}}}};if(!B(_es(_zi,39))){return new F(function(){return _CV(_,_CN,_CO,_CP,_CQ,_CR,_CS,_CT,_CU);});}else{var _Fw=_CO+1|0;switch(E(B(_vM(_Fw,_CP,_CR)))){case 35:var _Fx=new T(function(){return E(_CT)+1|0;});return new F(function(){return _CV(_,_CN,_Fw,_CP,_CQ,_CR,_CS,_Fx,_CU);});break;case 45:var _Fy=new T(function(){return E(_CT)+1|0;});return new F(function(){return _CV(_,_CN,_Fw,_CP,_CQ,_CR,_CS,_Fy,_CU);});break;default:return new F(function(){return _CV(_,_CN,_CO,_CP,_CQ,_CR,_CS,_CT,_CU);});}}};if(!B(_es(_zi,37))){return new F(function(){return _CM(_,_CE,_CF,_CG,_CH,_CI,_CJ,_CK,_CL);});}else{var _Fz=_CF+(-1)|0;switch(E(B(_vM(_Fz,_CG,_CI)))){case 35:var _FA=new T(function(){return E(_CK)+1|0;});return new F(function(){return _CM(_,_CE,_Fz,_CG,_CH,_CI,_CJ,_FA,_CL);});break;case 45:var _FB=new T(function(){return E(_CK)+1|0;});return new F(function(){return _CM(_,_CE,_Fz,_CG,_CH,_CI,_CJ,_FB,_CL);});break;default:return new F(function(){return _CM(_,_CE,_CF,_CG,_CH,_CI,_CJ,_CK,_CL);});}}};if(!B(_es(_zi,40))){var _FC=function(_,_FD,_FE,_FF,_FG,_FH,_FI,_FJ,_FK){var _FL=function(_,_FM,_FN,_FO,_FP,_FQ,_FR,_FS,_FT){var _FU=jsFind(toJSStr(E(_ym)));if(!_FU[0]){return new F(function(){return die(_yi);});}else{var _FV=new T(function(){var _FW=function(_FX){while(1){var _FY=(function(_FZ){var _G0=E(_FZ);if(!_G0[0]){return [0];}else{var _G1=_G0[2],_G2=E(_G0[1]);if(!_G2[0]){_FX=_G1;return null;}else{var _G3=E(_G2[2]);if(!_G3[0]){_FX=_G1;return null;}else{if(!E(_G3[2])[0]){var _G4=E(_G2[1]);if(0>(_FN+_G4|0)){var _G5=function(_G6){while(1){var _G7=(function(_G8){var _G9=E(_G8);if(!_G9[0]){return [0];}else{var _Ga=_G9[2],_Gb=E(_G9[1]);if(!_Gb[0]){_G6=_Ga;return null;}else{var _Gc=E(_Gb[2]);if(!_Gc[0]){_G6=_Ga;return null;}else{if(!E(_Gc[2])[0]){var _Gd=E(_Gb[1]);if(0>(_FN+_Gd|0)){_G6=_Ga;return null;}else{if((_FN+_Gd|0)>44){_G6=_Ga;return null;}else{var _Ge=E(_FO),_Gf=E(_Gc[1]);if(0>(_Ge+_Gf|0)){_G6=_Ga;return null;}else{if((_Ge+_Gf|0)>34){_G6=_Ga;return null;}else{var _Gg=new T(function(){return B(_G5(_Ga));}),_Gh=_FN+_Gd|0,_Gi=_Ge+_Gf|0,_Gj=new T(function(){return B(_qO(_Gh,_Gi,_FQ));});return [1,[0,[0,_Gh,_Gi],_Gj],_Gg];}}}}}else{_G6=_Ga;return null;}}}}})(_G6);if(_G7!=null){return _G7;}}};return new F(function(){return _G5(_G1);});}else{if((_FN+_G4|0)>44){var _Gk=function(_Gl){while(1){var _Gm=(function(_Gn){var _Go=E(_Gn);if(!_Go[0]){return [0];}else{var _Gp=_Go[2],_Gq=E(_Go[1]);if(!_Gq[0]){_Gl=_Gp;return null;}else{var _Gr=E(_Gq[2]);if(!_Gr[0]){_Gl=_Gp;return null;}else{if(!E(_Gr[2])[0]){var _Gs=E(_Gq[1]);if(0>(_FN+_Gs|0)){_Gl=_Gp;return null;}else{if((_FN+_Gs|0)>44){_Gl=_Gp;return null;}else{var _Gt=E(_FO),_Gu=E(_Gr[1]);if(0>(_Gt+_Gu|0)){_Gl=_Gp;return null;}else{if((_Gt+_Gu|0)>34){_Gl=_Gp;return null;}else{var _Gv=new T(function(){return B(_Gk(_Gp));}),_Gw=_FN+_Gs|0,_Gx=_Gt+_Gu|0,_Gy=new T(function(){return B(_qO(_Gw,_Gx,_FQ));});return [1,[0,[0,_Gw,_Gx],_Gy],_Gv];}}}}}else{_Gl=_Gp;return null;}}}}})(_Gl);if(_Gm!=null){return _Gm;}}};return new F(function(){return _Gk(_G1);});}else{var _Gz=E(_FO),_GA=E(_G3[1]);if(0>(_Gz+_GA|0)){var _GB=function(_GC){while(1){var _GD=(function(_GE){var _GF=E(_GE);if(!_GF[0]){return [0];}else{var _GG=_GF[2],_GH=E(_GF[1]);if(!_GH[0]){_GC=_GG;return null;}else{var _GI=E(_GH[2]);if(!_GI[0]){_GC=_GG;return null;}else{if(!E(_GI[2])[0]){var _GJ=E(_GH[1]);if(0>(_FN+_GJ|0)){_GC=_GG;return null;}else{if((_FN+_GJ|0)>44){_GC=_GG;return null;}else{var _GK=E(_GI[1]);if(0>(_Gz+_GK|0)){_GC=_GG;return null;}else{if((_Gz+_GK|0)>34){_GC=_GG;return null;}else{var _GL=new T(function(){return B(_GB(_GG));}),_GM=_FN+_GJ|0,_GN=_Gz+_GK|0,_GO=new T(function(){return B(_qO(_GM,_GN,_FQ));});return [1,[0,[0,_GM,_GN],_GO],_GL];}}}}}else{_GC=_GG;return null;}}}}})(_GC);if(_GD!=null){return _GD;}}};return new F(function(){return _GB(_G1);});}else{if((_Gz+_GA|0)>34){var _GP=function(_GQ){while(1){var _GR=(function(_GS){var _GT=E(_GS);if(!_GT[0]){return [0];}else{var _GU=_GT[2],_GV=E(_GT[1]);if(!_GV[0]){_GQ=_GU;return null;}else{var _GW=E(_GV[2]);if(!_GW[0]){_GQ=_GU;return null;}else{if(!E(_GW[2])[0]){var _GX=E(_GV[1]);if(0>(_FN+_GX|0)){_GQ=_GU;return null;}else{if((_FN+_GX|0)>44){_GQ=_GU;return null;}else{var _GY=E(_GW[1]);if(0>(_Gz+_GY|0)){_GQ=_GU;return null;}else{if((_Gz+_GY|0)>34){_GQ=_GU;return null;}else{var _GZ=new T(function(){return B(_GP(_GU));}),_H0=_FN+_GX|0,_H1=_Gz+_GY|0,_H2=new T(function(){return B(_qO(_H0,_H1,_FQ));});return [1,[0,[0,_H0,_H1],_H2],_GZ];}}}}}else{_GQ=_GU;return null;}}}}})(_GQ);if(_GR!=null){return _GR;}}};return new F(function(){return _GP(_G1);});}else{var _H3=new T(function(){var _H4=function(_H5){while(1){var _H6=(function(_H7){var _H8=E(_H7);if(!_H8[0]){return [0];}else{var _H9=_H8[2],_Ha=E(_H8[1]);if(!_Ha[0]){_H5=_H9;return null;}else{var _Hb=E(_Ha[2]);if(!_Hb[0]){_H5=_H9;return null;}else{if(!E(_Hb[2])[0]){var _Hc=E(_Ha[1]);if(0>(_FN+_Hc|0)){_H5=_H9;return null;}else{if((_FN+_Hc|0)>44){_H5=_H9;return null;}else{var _Hd=E(_Hb[1]);if(0>(_Gz+_Hd|0)){_H5=_H9;return null;}else{if((_Gz+_Hd|0)>34){_H5=_H9;return null;}else{var _He=new T(function(){return B(_H4(_H9));}),_Hf=_FN+_Hc|0,_Hg=_Gz+_Hd|0,_Hh=new T(function(){return B(_qO(_Hf,_Hg,_FQ));});return [1,[0,[0,_Hf,_Hg],_Hh],_He];}}}}}else{_H5=_H9;return null;}}}}})(_H5);if(_H6!=null){return _H6;}}};return B(_H4(_G1));}),_Hi=_FN+_G4|0,_Hj=_Gz+_GA|0,_Hk=new T(function(){return B(_qO(_Hi,_Hj,_FQ));});return [1,[0,[0,_Hi,_Hj],_Hk],_H3];}}}}}else{_FX=_G1;return null;}}}}})(_FX);if(_FY!=null){return _FY;}}};return B(_xv(_qL,B(_FW(_yc)),_FR));}),_Hl=new T(function(){var _Hm=E(_FO);if(0>=_Hm){if(0>=_FN){return E(_vY);}else{return B(_w0(_FN));}}else{var _Hn=new T(function(){var _Ho=new T(function(){if(0>=_FN){return E(_vY);}else{return B(_w0(_FN));}},1);return B(_v(_wn,_Ho));}),_Hp=function(_Hq){var _Hr=E(_Hq);if(_Hr==1){return E(_Hn);}else{var _Hs=new T(function(){return B(_Hp(_Hr-1|0));},1);return new F(function(){return _v(_wn,_Hs);});}};return B(_Hp(_Hm));}}),_Ht=B(A(_l3,[_4d,_sN,_FU[1],_l2,_Hl,[0,_FM,[0,_FN,_FO],_FP,_FQ,_FV,_FS,_FT],_])),_Hu=_Ht,_Hv=E(_w5),_Hw=jsFind(_Hv);if(!_Hw[0]){return new F(function(){return _zd(_Hv);});}else{var _Hx=new T(function(){return E(E(_Hu)[2]);}),_Hy=new T(function(){var _Hz=new T(function(){return E(E(_Hx)[5]);});return B(_wW(_Hz));}),_HA=B(A(_l3,[_4d,_sN,_Hw[1],_l2,_Hy,_Hx,_])),_HB=E(E(_HA)[2]);if(E(_HB[6])==5){var _HC=E(_3z),_HD=E(_wi)(_HC),_HE=E(_wg),_HF=toJSStr(E(_yj)),_HG=jsQuerySelectorAll(_HE,_HF);if(!_HG[0]){return E(_yf);}else{if(!E(_HG[2])[0]){var _HH=E(_wj),_HI=_HH(E(_HG[1])),_HJ=B(A(_kq,[_4d,_sN,_HI,_yo,_xD,[0,_HB[1],_HB[2],_HB[3],_HB[4],_HB[5],_wf,_HB[7]],_])),_HK=_HJ,_HL=E(_w6),_HM=jsFind(_HL);if(!_HM[0]){return new F(function(){return _zd(_HL);});}else{var _HN=_HM[1],_HO=E(_zh),_HP=new T(function(){return E(E(_HK)[2]);}),_HQ=B(_v5(_HN,_HO,_HP,_)),_HR=_HQ,_HS=E(_HN),_HT=jsQuerySelectorAll(_HS,toJSStr(_yl));if(!_HT[0]){return E(_tZ);}else{var _HU=_HT[1];if(!E(_HT[2])[0]){var _HV=function(_HW,_){var _HX=rMV(_HO),_HY=E(_HX),_HZ=E(_HY[7]),_I0=B(_iY(_HZ[1],_HZ[2],_HZ[3],_HZ[4],_HZ[5],_)),_=wMV(_HO,[0,_HY[1],_HY[2],_HY[3],_HY[4],_HY[5],_HY[6],E(_I0)[2]]),_I1=rMV(_HO);if(!B(_wk(B(_wI(_yr,E(E(_I1)[7])[2]))))){var _I2=rMV(_HO),_I3=_I2,_I4=new T(function(){return E(E(_I3)[7]);});return new F(function(){return _n2(_HS,_I4,_);});}else{var _I5=E(_wh)(_HC),_I6=jsQuerySelectorAll(_HE,_HF);if(!_I6[0]){return new F(function(){return _sO(_);});}else{if(!E(_I6[2])[0]){var _I7=_HH(E(_I6[1])),_I8=B(A(_kq,[_4d,_4S,_I7,_yo,_yn,_])),_I9=E(_HU),_Ia=jsQuerySelectorAll(_I9,toJSStr(E(_yq))),_Ib=B(_w7(_Ia,_)),_Ic=jsQuerySelectorAll(_I9,toJSStr(E(_yp))),_Id=B(_wb(_Ic,_)),_Ie=rMV(_HO),_If=_Ie,_Ig=new T(function(){return E(E(_If)[7]);});return new F(function(){return _n2(_HS,_Ig,_);});}else{return new F(function(){return _sO(_);});}}}},_Ih=B(A(_yE,[_4T,_4d,_46,_HU,_w4,_HV,_])),_Ii=new T(function(){return E(E(_HR)[2]);});return [0,_47,_Ii];}else{return E(_tZ);}}}}else{return E(_yf);}}}else{return [0,_47,_HB];}}}};if(!B(_es(_zi,39))){return new F(function(){return _FL(_,_FD,_FE,_FF,_FG,_FH,_FI,_FJ,_FK);});}else{var _Ij=_FE+1|0;switch(E(B(_vM(_Ij,_FF,_FH)))){case 35:var _Ik=new T(function(){return E(_FJ)+1|0;});return new F(function(){return _FL(_,_FD,_Ij,_FF,_FG,_FH,_FI,_Ik,_FK);});break;case 45:var _Il=new T(function(){return E(_FJ)+1|0;});return new F(function(){return _FL(_,_FD,_Ij,_FF,_FG,_FH,_FI,_Il,_FK);});break;default:return new F(function(){return _FL(_,_FD,_FE,_FF,_FG,_FH,_FI,_FJ,_FK);});}}};if(!B(_es(_zi,37))){var _Im=function(_,_In,_Io,_Ip,_Iq,_Ir,_Is,_It,_Iu){var _Iv=jsFind(toJSStr(E(_ym)));if(!_Iv[0]){return new F(function(){return die(_yi);});}else{var _Iw=new T(function(){var _Ix=function(_Iy){while(1){var _Iz=(function(_IA){var _IB=E(_IA);if(!_IB[0]){return [0];}else{var _IC=_IB[2],_ID=E(_IB[1]);if(!_ID[0]){_Iy=_IC;return null;}else{var _IE=E(_ID[2]);if(!_IE[0]){_Iy=_IC;return null;}else{if(!E(_IE[2])[0]){var _IF=E(_ID[1]);if(0>(_Io+_IF|0)){var _IG=function(_IH){while(1){var _II=(function(_IJ){var _IK=E(_IJ);if(!_IK[0]){return [0];}else{var _IL=_IK[2],_IM=E(_IK[1]);if(!_IM[0]){_IH=_IL;return null;}else{var _IN=E(_IM[2]);if(!_IN[0]){_IH=_IL;return null;}else{if(!E(_IN[2])[0]){var _IO=E(_IM[1]);if(0>(_Io+_IO|0)){_IH=_IL;return null;}else{if((_Io+_IO|0)>44){_IH=_IL;return null;}else{var _IP=E(_Ip),_IQ=E(_IN[1]);if(0>(_IP+_IQ|0)){_IH=_IL;return null;}else{if((_IP+_IQ|0)>34){_IH=_IL;return null;}else{var _IR=new T(function(){return B(_IG(_IL));}),_IS=_Io+_IO|0,_IT=_IP+_IQ|0,_IU=new T(function(){return B(_qO(_IS,_IT,_Ir));});return [1,[0,[0,_IS,_IT],_IU],_IR];}}}}}else{_IH=_IL;return null;}}}}})(_IH);if(_II!=null){return _II;}}};return new F(function(){return _IG(_IC);});}else{if((_Io+_IF|0)>44){var _IV=function(_IW){while(1){var _IX=(function(_IY){var _IZ=E(_IY);if(!_IZ[0]){return [0];}else{var _J0=_IZ[2],_J1=E(_IZ[1]);if(!_J1[0]){_IW=_J0;return null;}else{var _J2=E(_J1[2]);if(!_J2[0]){_IW=_J0;return null;}else{if(!E(_J2[2])[0]){var _J3=E(_J1[1]);if(0>(_Io+_J3|0)){_IW=_J0;return null;}else{if((_Io+_J3|0)>44){_IW=_J0;return null;}else{var _J4=E(_Ip),_J5=E(_J2[1]);if(0>(_J4+_J5|0)){_IW=_J0;return null;}else{if((_J4+_J5|0)>34){_IW=_J0;return null;}else{var _J6=new T(function(){return B(_IV(_J0));}),_J7=_Io+_J3|0,_J8=_J4+_J5|0,_J9=new T(function(){return B(_qO(_J7,_J8,_Ir));});return [1,[0,[0,_J7,_J8],_J9],_J6];}}}}}else{_IW=_J0;return null;}}}}})(_IW);if(_IX!=null){return _IX;}}};return new F(function(){return _IV(_IC);});}else{var _Ja=E(_Ip),_Jb=E(_IE[1]);if(0>(_Ja+_Jb|0)){var _Jc=function(_Jd){while(1){var _Je=(function(_Jf){var _Jg=E(_Jf);if(!_Jg[0]){return [0];}else{var _Jh=_Jg[2],_Ji=E(_Jg[1]);if(!_Ji[0]){_Jd=_Jh;return null;}else{var _Jj=E(_Ji[2]);if(!_Jj[0]){_Jd=_Jh;return null;}else{if(!E(_Jj[2])[0]){var _Jk=E(_Ji[1]);if(0>(_Io+_Jk|0)){_Jd=_Jh;return null;}else{if((_Io+_Jk|0)>44){_Jd=_Jh;return null;}else{var _Jl=E(_Jj[1]);if(0>(_Ja+_Jl|0)){_Jd=_Jh;return null;}else{if((_Ja+_Jl|0)>34){_Jd=_Jh;return null;}else{var _Jm=new T(function(){return B(_Jc(_Jh));}),_Jn=_Io+_Jk|0,_Jo=_Ja+_Jl|0,_Jp=new T(function(){return B(_qO(_Jn,_Jo,_Ir));});return [1,[0,[0,_Jn,_Jo],_Jp],_Jm];}}}}}else{_Jd=_Jh;return null;}}}}})(_Jd);if(_Je!=null){return _Je;}}};return new F(function(){return _Jc(_IC);});}else{if((_Ja+_Jb|0)>34){var _Jq=function(_Jr){while(1){var _Js=(function(_Jt){var _Ju=E(_Jt);if(!_Ju[0]){return [0];}else{var _Jv=_Ju[2],_Jw=E(_Ju[1]);if(!_Jw[0]){_Jr=_Jv;return null;}else{var _Jx=E(_Jw[2]);if(!_Jx[0]){_Jr=_Jv;return null;}else{if(!E(_Jx[2])[0]){var _Jy=E(_Jw[1]);if(0>(_Io+_Jy|0)){_Jr=_Jv;return null;}else{if((_Io+_Jy|0)>44){_Jr=_Jv;return null;}else{var _Jz=E(_Jx[1]);if(0>(_Ja+_Jz|0)){_Jr=_Jv;return null;}else{if((_Ja+_Jz|0)>34){_Jr=_Jv;return null;}else{var _JA=new T(function(){return B(_Jq(_Jv));}),_JB=_Io+_Jy|0,_JC=_Ja+_Jz|0,_JD=new T(function(){return B(_qO(_JB,_JC,_Ir));});return [1,[0,[0,_JB,_JC],_JD],_JA];}}}}}else{_Jr=_Jv;return null;}}}}})(_Jr);if(_Js!=null){return _Js;}}};return new F(function(){return _Jq(_IC);});}else{var _JE=new T(function(){var _JF=function(_JG){while(1){var _JH=(function(_JI){var _JJ=E(_JI);if(!_JJ[0]){return [0];}else{var _JK=_JJ[2],_JL=E(_JJ[1]);if(!_JL[0]){_JG=_JK;return null;}else{var _JM=E(_JL[2]);if(!_JM[0]){_JG=_JK;return null;}else{if(!E(_JM[2])[0]){var _JN=E(_JL[1]);if(0>(_Io+_JN|0)){_JG=_JK;return null;}else{if((_Io+_JN|0)>44){_JG=_JK;return null;}else{var _JO=E(_JM[1]);if(0>(_Ja+_JO|0)){_JG=_JK;return null;}else{if((_Ja+_JO|0)>34){_JG=_JK;return null;}else{var _JP=new T(function(){return B(_JF(_JK));}),_JQ=_Io+_JN|0,_JR=_Ja+_JO|0,_JS=new T(function(){return B(_qO(_JQ,_JR,_Ir));});return [1,[0,[0,_JQ,_JR],_JS],_JP];}}}}}else{_JG=_JK;return null;}}}}})(_JG);if(_JH!=null){return _JH;}}};return B(_JF(_IC));}),_JT=_Io+_IF|0,_JU=_Ja+_Jb|0,_JV=new T(function(){return B(_qO(_JT,_JU,_Ir));});return [1,[0,[0,_JT,_JU],_JV],_JE];}}}}}else{_Iy=_IC;return null;}}}}})(_Iy);if(_Iz!=null){return _Iz;}}};return B(_xv(_qL,B(_Ix(_yc)),_Is));}),_JW=new T(function(){var _JX=E(_Ip);if(0>=_JX){if(0>=_Io){return E(_vY);}else{return B(_w0(_Io));}}else{var _JY=new T(function(){var _JZ=new T(function(){if(0>=_Io){return E(_vY);}else{return B(_w0(_Io));}},1);return B(_v(_wn,_JZ));}),_K0=function(_K1){var _K2=E(_K1);if(_K2==1){return E(_JY);}else{var _K3=new T(function(){return B(_K0(_K2-1|0));},1);return new F(function(){return _v(_wn,_K3);});}};return B(_K0(_JX));}}),_K4=B(A(_l3,[_4d,_sN,_Iv[1],_l2,_JW,[0,_In,[0,_Io,_Ip],_Iq,_Ir,_Iw,_It,_Iu],_])),_K5=_K4,_K6=E(_w5),_K7=jsFind(_K6);if(!_K7[0]){return new F(function(){return _zd(_K6);});}else{var _K8=new T(function(){return E(E(_K5)[2]);}),_K9=new T(function(){var _Ka=new T(function(){return E(E(_K8)[5]);});return B(_wW(_Ka));}),_Kb=B(A(_l3,[_4d,_sN,_K7[1],_l2,_K9,_K8,_])),_Kc=E(E(_Kb)[2]);if(E(_Kc[6])==5){var _Kd=E(_3z),_Ke=E(_wi)(_Kd),_Kf=E(_wg),_Kg=toJSStr(E(_yj)),_Kh=jsQuerySelectorAll(_Kf,_Kg);if(!_Kh[0]){return E(_yf);}else{if(!E(_Kh[2])[0]){var _Ki=E(_wj),_Kj=_Ki(E(_Kh[1])),_Kk=B(A(_kq,[_4d,_sN,_Kj,_yo,_xD,[0,_Kc[1],_Kc[2],_Kc[3],_Kc[4],_Kc[5],_wf,_Kc[7]],_])),_Kl=_Kk,_Km=E(_w6),_Kn=jsFind(_Km);if(!_Kn[0]){return new F(function(){return _zd(_Km);});}else{var _Ko=_Kn[1],_Kp=E(_zh),_Kq=new T(function(){return E(E(_Kl)[2]);}),_Kr=B(_v5(_Ko,_Kp,_Kq,_)),_Ks=_Kr,_Kt=E(_Ko),_Ku=jsQuerySelectorAll(_Kt,toJSStr(_yl));if(!_Ku[0]){return E(_tZ);}else{var _Kv=_Ku[1];if(!E(_Ku[2])[0]){var _Kw=function(_Kx,_){var _Ky=rMV(_Kp),_Kz=E(_Ky),_KA=E(_Kz[7]),_KB=B(_iY(_KA[1],_KA[2],_KA[3],_KA[4],_KA[5],_)),_=wMV(_Kp,[0,_Kz[1],_Kz[2],_Kz[3],_Kz[4],_Kz[5],_Kz[6],E(_KB)[2]]),_KC=rMV(_Kp);if(!B(_wk(B(_wI(_yr,E(E(_KC)[7])[2]))))){var _KD=rMV(_Kp),_KE=_KD,_KF=new T(function(){return E(E(_KE)[7]);});return new F(function(){return _n2(_Kt,_KF,_);});}else{var _KG=E(_wh)(_Kd),_KH=jsQuerySelectorAll(_Kf,_Kg);if(!_KH[0]){return new F(function(){return _sO(_);});}else{if(!E(_KH[2])[0]){var _KI=_Ki(E(_KH[1])),_KJ=B(A(_kq,[_4d,_4S,_KI,_yo,_yn,_])),_KK=E(_Kv),_KL=jsQuerySelectorAll(_KK,toJSStr(E(_yq))),_KM=B(_w7(_KL,_)),_KN=jsQuerySelectorAll(_KK,toJSStr(E(_yp))),_KO=B(_wb(_KN,_)),_KP=rMV(_Kp),_KQ=_KP,_KR=new T(function(){return E(E(_KQ)[7]);});return new F(function(){return _n2(_Kt,_KR,_);});}else{return new F(function(){return _sO(_);});}}}},_KS=B(A(_yE,[_4T,_4d,_46,_Kv,_w4,_Kw,_])),_KT=new T(function(){return E(E(_Ks)[2]);});return [0,_47,_KT];}else{return E(_tZ);}}}}else{return E(_yf);}}}else{return [0,_47,_Kc];}}}};if(!B(_es(_zi,39))){var _KU=jsFind(toJSStr(E(_ym)));if(!_KU[0]){return new F(function(){return die(_yi);});}else{var _KV=new T(function(){var _KW=function(_KX){while(1){var _KY=(function(_KZ){var _L0=E(_KZ);if(!_L0[0]){return [0];}else{var _L1=_L0[2],_L2=E(_L0[1]);if(!_L2[0]){_KX=_L1;return null;}else{var _L3=E(_L2[2]);if(!_L3[0]){_KX=_L1;return null;}else{if(!E(_L3[2])[0]){var _L4=E(_zp),_L5=E(_L2[1]);if(0>(_L4+_L5|0)){var _L6=function(_L7){while(1){var _L8=(function(_L9){var _La=E(_L9);if(!_La[0]){return [0];}else{var _Lb=_La[2],_Lc=E(_La[1]);if(!_Lc[0]){_L7=_Lb;return null;}else{var _Ld=E(_Lc[2]);if(!_Ld[0]){_L7=_Lb;return null;}else{if(!E(_Ld[2])[0]){var _Le=E(_Lc[1]);if(0>(_L4+_Le|0)){_L7=_Lb;return null;}else{if((_L4+_Le|0)>44){_L7=_Lb;return null;}else{var _Lf=E(_zq),_Lg=E(_Ld[1]);if(0>(_Lf+_Lg|0)){_L7=_Lb;return null;}else{if((_Lf+_Lg|0)>34){_L7=_Lb;return null;}else{var _Lh=new T(function(){return B(_L6(_Lb));}),_Li=_L4+_Le|0,_Lj=_Lf+_Lg|0,_Lk=new T(function(){return B(_qO(_Li,_Lj,_zk));});return [1,[0,[0,_Li,_Lj],_Lk],_Lh];}}}}}else{_L7=_Lb;return null;}}}}})(_L7);if(_L8!=null){return _L8;}}};return new F(function(){return _L6(_L1);});}else{if((_L4+_L5|0)>44){var _Ll=function(_Lm){while(1){var _Ln=(function(_Lo){var _Lp=E(_Lo);if(!_Lp[0]){return [0];}else{var _Lq=_Lp[2],_Lr=E(_Lp[1]);if(!_Lr[0]){_Lm=_Lq;return null;}else{var _Ls=E(_Lr[2]);if(!_Ls[0]){_Lm=_Lq;return null;}else{if(!E(_Ls[2])[0]){var _Lt=E(_Lr[1]);if(0>(_L4+_Lt|0)){_Lm=_Lq;return null;}else{if((_L4+_Lt|0)>44){_Lm=_Lq;return null;}else{var _Lu=E(_zq),_Lv=E(_Ls[1]);if(0>(_Lu+_Lv|0)){_Lm=_Lq;return null;}else{if((_Lu+_Lv|0)>34){_Lm=_Lq;return null;}else{var _Lw=new T(function(){return B(_Ll(_Lq));}),_Lx=_L4+_Lt|0,_Ly=_Lu+_Lv|0,_Lz=new T(function(){return B(_qO(_Lx,_Ly,_zk));});return [1,[0,[0,_Lx,_Ly],_Lz],_Lw];}}}}}else{_Lm=_Lq;return null;}}}}})(_Lm);if(_Ln!=null){return _Ln;}}};return new F(function(){return _Ll(_L1);});}else{var _LA=E(_zq),_LB=E(_L3[1]);if(0>(_LA+_LB|0)){var _LC=function(_LD){while(1){var _LE=(function(_LF){var _LG=E(_LF);if(!_LG[0]){return [0];}else{var _LH=_LG[2],_LI=E(_LG[1]);if(!_LI[0]){_LD=_LH;return null;}else{var _LJ=E(_LI[2]);if(!_LJ[0]){_LD=_LH;return null;}else{if(!E(_LJ[2])[0]){var _LK=E(_LI[1]);if(0>(_L4+_LK|0)){_LD=_LH;return null;}else{if((_L4+_LK|0)>44){_LD=_LH;return null;}else{var _LL=E(_LJ[1]);if(0>(_LA+_LL|0)){_LD=_LH;return null;}else{if((_LA+_LL|0)>34){_LD=_LH;return null;}else{var _LM=new T(function(){return B(_LC(_LH));}),_LN=_L4+_LK|0,_LO=_LA+_LL|0,_LP=new T(function(){return B(_qO(_LN,_LO,_zk));});return [1,[0,[0,_LN,_LO],_LP],_LM];}}}}}else{_LD=_LH;return null;}}}}})(_LD);if(_LE!=null){return _LE;}}};return new F(function(){return _LC(_L1);});}else{if((_LA+_LB|0)>34){var _LQ=function(_LR){while(1){var _LS=(function(_LT){var _LU=E(_LT);if(!_LU[0]){return [0];}else{var _LV=_LU[2],_LW=E(_LU[1]);if(!_LW[0]){_LR=_LV;return null;}else{var _LX=E(_LW[2]);if(!_LX[0]){_LR=_LV;return null;}else{if(!E(_LX[2])[0]){var _LY=E(_LW[1]);if(0>(_L4+_LY|0)){_LR=_LV;return null;}else{if((_L4+_LY|0)>44){_LR=_LV;return null;}else{var _LZ=E(_LX[1]);if(0>(_LA+_LZ|0)){_LR=_LV;return null;}else{if((_LA+_LZ|0)>34){_LR=_LV;return null;}else{var _M0=new T(function(){return B(_LQ(_LV));}),_M1=_L4+_LY|0,_M2=_LA+_LZ|0,_M3=new T(function(){return B(_qO(_M1,_M2,_zk));});return [1,[0,[0,_M1,_M2],_M3],_M0];}}}}}else{_LR=_LV;return null;}}}}})(_LR);if(_LS!=null){return _LS;}}};return new F(function(){return _LQ(_L1);});}else{var _M4=new T(function(){var _M5=function(_M6){while(1){var _M7=(function(_M8){var _M9=E(_M8);if(!_M9[0]){return [0];}else{var _Ma=_M9[2],_Mb=E(_M9[1]);if(!_Mb[0]){_M6=_Ma;return null;}else{var _Mc=E(_Mb[2]);if(!_Mc[0]){_M6=_Ma;return null;}else{if(!E(_Mc[2])[0]){var _Md=E(_Mb[1]);if(0>(_L4+_Md|0)){_M6=_Ma;return null;}else{if((_L4+_Md|0)>44){_M6=_Ma;return null;}else{var _Me=E(_Mc[1]);if(0>(_LA+_Me|0)){_M6=_Ma;return null;}else{if((_LA+_Me|0)>34){_M6=_Ma;return null;}else{var _Mf=new T(function(){return B(_M5(_Ma));}),_Mg=_L4+_Md|0,_Mh=_LA+_Me|0,_Mi=new T(function(){return B(_qO(_Mg,_Mh,_zk));});return [1,[0,[0,_Mg,_Mh],_Mi],_Mf];}}}}}else{_M6=_Ma;return null;}}}}})(_M6);if(_M7!=null){return _M7;}}};return B(_M5(_L1));}),_Mj=_L4+_L5|0,_Mk=_LA+_LB|0,_Ml=new T(function(){return B(_qO(_Mj,_Mk,_zk));});return [1,[0,[0,_Mj,_Mk],_Ml],_M4];}}}}}else{_KX=_L1;return null;}}}}})(_KX);if(_KY!=null){return _KY;}}};return B(_xv(_qL,B(_KW(_yc)),_zl));}),_Mm=new T(function(){var _Mn=E(_zq);if(0>=_Mn){var _Mo=E(_zp);if(0>=_Mo){return E(_vY);}else{return B(_w0(_Mo));}}else{var _Mp=new T(function(){var _Mq=new T(function(){var _Mr=E(_zp);if(0>=_Mr){return E(_vY);}else{return B(_w0(_Mr));}},1);return B(_v(_wn,_Mq));}),_Ms=function(_Mt){var _Mu=E(_Mt);if(_Mu==1){return E(_Mp);}else{var _Mv=new T(function(){return B(_Ms(_Mu-1|0));},1);return new F(function(){return _v(_wn,_Mv);});}};return B(_Ms(_Mn));}}),_Mw=B(A(_l3,[_4d,_sN,_KU[1],_l2,_Mm,[0,_zi,[0,_zp,_zq],_zo,_zk,_KV,_zm,_zn],_])),_Mx=_Mw,_My=E(_w5),_Mz=jsFind(_My);if(!_Mz[0]){return new F(function(){return _zd(_My);});}else{var _MA=new T(function(){return E(E(_Mx)[2]);}),_MB=new T(function(){var _MC=new T(function(){return E(E(_MA)[5]);});return B(_wW(_MC));}),_MD=B(A(_l3,[_4d,_sN,_Mz[1],_l2,_MB,_MA,_])),_ME=E(E(_MD)[2]);if(E(_ME[6])==5){var _MF=E(_3z),_MG=E(_wi)(_MF),_MH=E(_wg),_MI=toJSStr(E(_yj)),_MJ=jsQuerySelectorAll(_MH,_MI);if(!_MJ[0]){return E(_yf);}else{if(!E(_MJ[2])[0]){var _MK=E(_wj),_ML=_MK(E(_MJ[1])),_MM=B(A(_kq,[_4d,_sN,_ML,_yo,_xD,[0,_ME[1],_ME[2],_ME[3],_ME[4],_ME[5],_wf,_ME[7]],_])),_MN=_MM,_MO=E(_w6),_MP=jsFind(_MO);if(!_MP[0]){return new F(function(){return _zd(_MO);});}else{var _MQ=_MP[1],_MR=E(_zh),_MS=new T(function(){return E(E(_MN)[2]);}),_MT=B(_v5(_MQ,_MR,_MS,_)),_MU=_MT,_MV=E(_MQ),_MW=jsQuerySelectorAll(_MV,toJSStr(_yl));if(!_MW[0]){return E(_tZ);}else{var _MX=_MW[1];if(!E(_MW[2])[0]){var _MY=function(_MZ,_){var _N0=rMV(_MR),_N1=E(_N0),_N2=E(_N1[7]),_N3=B(_iY(_N2[1],_N2[2],_N2[3],_N2[4],_N2[5],_)),_=wMV(_MR,[0,_N1[1],_N1[2],_N1[3],_N1[4],_N1[5],_N1[6],E(_N3)[2]]),_N4=rMV(_MR);if(!B(_wk(B(_wI(_yr,E(E(_N4)[7])[2]))))){var _N5=rMV(_MR),_N6=_N5,_N7=new T(function(){return E(E(_N6)[7]);});return new F(function(){return _n2(_MV,_N7,_);});}else{var _N8=E(_wh)(_MF),_N9=jsQuerySelectorAll(_MH,_MI);if(!_N9[0]){return new F(function(){return _sO(_);});}else{if(!E(_N9[2])[0]){var _Na=_MK(E(_N9[1])),_Nb=B(A(_kq,[_4d,_4S,_Na,_yo,_yn,_])),_Nc=E(_MX),_Nd=jsQuerySelectorAll(_Nc,toJSStr(E(_yq))),_Ne=B(_w7(_Nd,_)),_Nf=jsQuerySelectorAll(_Nc,toJSStr(E(_yp))),_Ng=B(_wb(_Nf,_)),_Nh=rMV(_MR),_Ni=_Nh,_Nj=new T(function(){return E(E(_Ni)[7]);});return new F(function(){return _n2(_MV,_Nj,_);});}else{return new F(function(){return _sO(_);});}}}},_Nk=B(A(_yE,[_4T,_4d,_46,_MX,_w4,_MY,_])),_Nl=new T(function(){return E(E(_MU)[2]);});return [0,_47,_Nl];}else{return E(_tZ);}}}}else{return E(_yf);}}}else{return [0,_47,_ME];}}}}else{var _Nm=E(_zp),_Nn=_Nm+1|0;switch(E(B(_vM(_Nn,_zq,_zk)))){case 35:var _No=new T(function(){return E(_zm)+1|0;});return new F(function(){return _Im(_,_zi,_Nn,_zq,_zo,_zk,_zl,_No,_zn);});break;case 45:var _Np=new T(function(){return E(_zm)+1|0;});return new F(function(){return _Im(_,_zi,_Nn,_zq,_zo,_zk,_zl,_Np,_zn);});break;default:return new F(function(){return _Im(_,_zi,_Nm,_zq,_zo,_zk,_zl,_zm,_zn);});}}}else{var _Nq=E(_zp),_Nr=_Nq+(-1)|0;switch(E(B(_vM(_Nr,_zq,_zk)))){case 35:var _Ns=new T(function(){return E(_zm)+1|0;});return new F(function(){return _FC(_,_zi,_Nr,_zq,_zo,_zk,_zl,_Ns,_zn);});break;case 45:var _Nt=new T(function(){return E(_zm)+1|0;});return new F(function(){return _FC(_,_zi,_Nr,_zq,_zo,_zk,_zl,_Nt,_zn);});break;default:return new F(function(){return _FC(_,_zi,_Nq,_zq,_zo,_zk,_zl,_zm,_zn);});}}}else{var _Nu=E(_zp),_Nv=new T(function(){return E(_zq)+1|0;});switch(E(B(_vM(_Nu,_Nv,_zk)))){case 35:var _Nw=new T(function(){return E(_zm)+1|0;});return new F(function(){return _CD(_,_zi,_Nu,_Nv,_zo,_zk,_zl,_Nw,_zn);});break;case 45:var _Nx=new T(function(){return E(_zm)+1|0;});return new F(function(){return _CD(_,_zi,_Nu,_Nv,_zo,_zk,_zl,_Nx,_zn);});break;default:return new F(function(){return _CD(_,_zi,_Nu,_zq,_zo,_zk,_zl,_zm,_zn);});}}}else{var _Ny=E(_zp),_Nz=new T(function(){return E(_zq)+(-1)|0;});switch(E(B(_vM(_Ny,_Nz,_zk)))){case 35:var _NA=new T(function(){return E(_zm)+1|0;});return new F(function(){return _zr(_,_zi,_Ny,_Nz,_zo,_zk,_zl,_NA,_zn);});break;case 45:var _NB=new T(function(){return E(_zm)+1|0;});return new F(function(){return _zr(_,_zi,_Ny,_Nz,_zo,_zk,_zl,_NB,_zn);});break;default:return new F(function(){return _zr(_,_zi,_Ny,_zq,_zo,_zk,_zl,_zm,_zn);});}}},_NC=function(_ND,_NE){while(1){var _NF=E(_ND);if(!_NF[0]){return (E(_NE)[0]==0)?true:false;}else{var _NG=E(_NE);if(!_NG[0]){return false;}else{if(E(_NF[1])!=E(_NG[1])){return false;}else{_ND=_NF[2];_NE=_NG[2];continue;}}}}},_NH=function(_NI,_NJ){return new F(function(){return _NC(E(_NI)[1],E(_NJ)[1]);});},_NK=function(_NL,_NM){while(1){var _NN=E(_NL);if(!_NN[0]){return E(_NM);}else{_NL=_NN[2];var _NO=_NM+1|0;_NM=_NO;continue;}}},_NP="party-display",_NQ="make-party",_NR=[2],_NS=new T(function(){return B(_wo(0,2147483647));}),_NT=function(_NU,_NV){var _NW=E(_NU);if(!_NW[0]){return [0];}else{var _NX=_NW[2],_NY=E(_NV);if(!_NY[0]){return [0];}else{var _NZ=_NY[2],_O0=new T(function(){return B(_NT(_NX,_NZ));});return [1,[0,_NW[1],_NY[1]],_O0];}}},_O1=new T(function(){return B(_NT(_NS,_11));}),_O2=function(_O3,_O4){while(1){var _O5=E(_O4);if(!_O5[0]){return E(_O3);}else{var _O6=E(_O5[1]),_O7=B(_gB(E(_O6[1]),_O6[2],_O3));_O4=_O5[2];_O3=_O7;continue;}}},_O8=new T(function(){return B(_O2(_NR,_O1));}),_O9=new T(function(){return B(_NK(_11,0));}),_Oa=0,_Ob=[0,_Oa,_O9,_O8],_Oc=30,_Od=1,_Oe=80,_Of=function(_Og,_Oh,_Oi){var _Oj=E(_Oi);if(!_Oj[0]){return [0];}else{var _Ok=_Oj[1],_Ol=_Oj[2];if(!B(A(_Og,[_Oh,_Ok]))){var _Om=new T(function(){return B(_Of(_Og,_Oh,_Ol));});return [1,_Ok,_Om];}else{return E(_Ol);}}},_On=10,_Oo=20,_Op=40,_Oq=function(_Or,_Os){var _Ot=function(_Ou,_Ov){while(1){var _Ow=(function(_Ox,_Oy){var _Oz=E(_Ox);if(!_Oz[0]){return [0];}else{var _OA=_Oz[2];if(!B(A(_Or,[_Oz[1]]))){_Ou=_OA;var _OB=_Oy+1|0;_Ov=_OB;return null;}else{var _OC=new T(function(){return B(_Ot(_OA,_Oy+1|0));});return [1,_Oy,_OC];}}})(_Ou,_Ov);if(_Ow!=null){return _Ow;}}},_OD=B(_Ot(_Os,0));return (_OD[0]==0)?[0]:[1,_OD[1]];},_OE=50,_OF=85,_OG=60,_OH=new T(function(){return B(unCStr("<button type=\"button\" class=\"btn btn-default btn-sm\" id=\"remove-party-go\">\u30e1\u30f3\u30d0\u30fc\u304b\u3089\u306f\u305a\u3059</button>"));}),_OI=new T(function(){return B(unAppCStr(")</button>&nbsp;",_OH));}),_OJ=new T(function(){return B(unCStr(" #join-party-btn"));}),_OK=new T(function(){return B(unCStr("#remove-party-go"));}),_OL=new T(function(){return B(unCStr("<button type=\"button\" class=\"btn btn-primary btn-sm\" disabled=\"disabled\">\u30d1\u30fc\u30c6\u30a3\u30e1\u30f3\u30d0\u30fc("));}),_OM=new T(function(){return B(unCStr("<button type=\"button\" class=\"btn btn-primary btn-sm\" disabled=\"disabled\">\u30d1\u30fc\u30c6\u30a3\u306b\u5165\u308c\u308b</button>"));}),_ON=new T(function(){return B(unCStr("#join-party-go"));}),_OO=new T(function(){return B(unCStr("<button type=\"button\" class=\"btn btn-primary btn-sm\" id=\"join-party-go\">\u30d1\u30fc\u30c6\u30a3\u306b\u5165\u308c\u308b</button>"));}),_OP=55,_OQ=70,_OR=45,_OS=new T(function(){return B(unCStr("\u30ae\u30e3\u30f3\u30d6\u30e9\u30fc"));}),_OT=[0,_OS,_Oc,_OR,_Oc,_OP,_OG,_OF,_Od,_OE,_OE,_OQ,_OQ,_Ob],_OU=35,_OV=65,_OW=new T(function(){return B(unCStr("\u8e0a\u308a\u5b50"));}),_OX=75,_OY=[0,_OW,_OV,_Oc,_OU,_OP,_OX,_Oe,_Od,_OP,_OP,_OV,_OV,_Ob],_OZ=[1,_OY,_11],_P0=[1,_OT,_OZ],_P1=25,_P2=90,_P3=new T(function(){return B(unCStr("\u546a\u8853\u5e2b"));}),_P4=[0,_P3,_Oo,_OV,_P2,_P1,_Oc,_OV,_Od,_Op,_Op,_Oe,_Oe,_Ob],_P5=[1,_P4,_P0],_P6=new T(function(){return B(unCStr("\u72c2\u4eba"));}),_P7=[0,_P6,_OF,_Oa,_Oa,_Oc,_On,_OG,_Od,_Oe,_Oe,_Oa,_Oa,_Ob],_P8=[1,_P7,_P5],_P9=new T(function(){return B(unCStr(","));}),_Pa=new T(function(){return B(unCStr("\u30d7\u30ea\u30f3\u30bb\u30b9"));}),_Pb=[0,_Pa,_On,_Oe,_OV,_Op,_OE,_Oo,_Od,_OG,_OG,_OE,_OE,_Ob],_Pc=new T(function(){return B(unCStr("\u885b\u5175"));}),_Pd=function(_Pe,_){var _Pf=rMV(_Pe),_Pg=_Pf,_Ph=E(_NP),_Pi=jsFind(_Ph);if(!_Pi[0]){return new F(function(){return _zd(_Ph);});}else{var _Pj=new T(function(){var _Pk=B(_wI(_lT,E(E(_Pg)[7])[1]));if(!_Pk[0]){return [0];}else{var _Pl=_Pk[2],_Pm=function(_Pn){var _Po=E(_Pn);if(!_Po[0]){return [0];}else{var _Pp=_Po[2],_Pq=new T(function(){return B(_Pm(_Pp));},1);return new F(function(){return _v(_Po[1],_Pq);});}},_Pr=function(_Ps,_Pt){var _Pu=new T(function(){return B(_Pm(_Pt));},1);return new F(function(){return _v(_Ps,_Pu);});},_Pv=new T(function(){return B(_wQ(_P9,_Pl));});return B(_Pr(_Pk[1],_Pv));}}),_Pw=B(A(_l3,[_4d,_4S,_Pi[1],_l2,_Pj,_])),_Px=E(_NQ),_Py=jsFind(_Px);if(!_Py[0]){return new F(function(){return _zd(_Px);});}else{var _Pz=E(_Py[1]),_PA=new T(function(){return B(_v(_Pa,_OJ));}),_PB=jsQuerySelectorAll(_Pz,toJSStr(B(unAppCStr("#character-detail-",_PA)))),_PC=function(_){var _PD=rMV(_Pe),_PE=E(_PD),_PF=_PE[7],_PG=new T(function(){var _PH=E(_PF),_PI=_PH[1],_PJ=new T(function(){return B(_v(_PI,[1,_Pb,_11]));});return [0,_PJ,_PH[2],_PH[3],_PH[4],_PH[5]];}),_=wMV(_Pe,[0,_PE[1],_PE[2],_PE[3],_PE[4],_PE[5],_PE[6],_PG]);return new F(function(){return _Pd(_Pe,_);});},_PK=function(_PL,_){return new F(function(){return _PC(_);});},_PM=function(_PN,_){while(1){var _PO=E(_PN);if(!_PO[0]){return _47;}else{var _PP=B(A(_yE,[_4T,_4d,_46,_PO[1],_w4,_PK,_]));_PN=_PO[2];continue;}}},_PQ=function(_){var _PR=rMV(_Pe),_PS=E(_PR),_PT=_PS[7],_PU=new T(function(){var _PV=E(_PT),_PW=_PV[1],_PX=new T(function(){return B(_Of(_NH,_Pb,_PW));});return [0,_PX,_PV[2],_PV[3],_PV[4],_PV[5]];}),_=wMV(_Pe,[0,_PS[1],_PS[2],_PS[3],_PS[4],_PS[5],_PS[6],_PU]);return new F(function(){return _Pd(_Pe,_);});},_PY=function(_PZ,_){return new F(function(){return _PQ(_);});},_Q0=function(_Q1,_){while(1){var _Q2=E(_Q1);if(!_Q2[0]){return _47;}else{var _Q3=B(A(_yE,[_4T,_4d,_46,_Q2[1],_w4,_PY,_]));_Q1=_Q2[2];continue;}}},_Q4=function(_Q5){return new F(function(){return _NC(_Pa,E(_Q5)[1]);});},_Q6=function(_Q7,_){while(1){var _Q8=(function(_Q9,_){var _Qa=E(_Q9);if(!_Qa[0]){return _47;}else{var _Qb=_Qa[1],_Qc=_Qa[2],_Qd=rMV(_Pe),_Qe=E(E(_Qd)[7])[1],_Qf=B(_Oq(_Q4,_Qe));if(!_Qf[0]){if(B(_NK(_Qe,0))<3){var _Qg=B(A(_l3,[_4d,_4S,_Qb,_l2,_OO,_])),_Qh=E(_ON),_Qi=jsQuerySelectorAll(E(_Qb),toJSStr(_Qh)),_Qj=B(_PM(_Qi,_)),_Qk=_Qc,_=_;while(1){var _Ql=(function(_Qm,_){var _Qn=E(_Qm);if(!_Qn[0]){return _47;}else{var _Qo=_Qn[1],_Qp=_Qn[2],_Qq=rMV(_Pe),_Qr=E(E(_Qq)[7])[1],_Qs=B(_Oq(_Q4,_Qr));if(!_Qs[0]){if(B(_NK(_Qr,0))<3){var _Qt=B(A(_l3,[_4d,_4S,_Qo,_l2,_OO,_])),_Qu=jsQuerySelectorAll(E(_Qo),toJSStr(_Qh)),_Qv=B(_PM(_Qu,_));_Qk=_Qp;return null;}else{var _Qw=B(A(_l3,[_4d,_4S,_Qo,_l2,_OM,_]));_Qk=_Qp;return null;}}else{var _Qx=_Qs[1],_Qy=new T(function(){var _Qz=new T(function(){return B(_v(B(_H(0,E(_Qx),_11)),_OI));},1);return B(_v(_OL,_Qz));}),_QA=B(A(_l3,[_4d,_4S,_Qo,_l2,_Qy,_])),_QB=jsQuerySelectorAll(E(_Qo),toJSStr(E(_OK))),_QC=B(_Q0(_QB,_));_Qk=_Qp;return null;}}})(_Qk,_);if(_Ql!=null){return _Ql;}}}else{var _QD=B(A(_l3,[_4d,_4S,_Qb,_l2,_OM,_]));_Q7=_Qc;return null;}}else{var _QE=_Qf[1],_QF=new T(function(){var _QG=new T(function(){return B(_v(B(_H(0,E(_QE),_11)),_OI));},1);return B(_v(_OL,_QG));}),_QH=B(A(_l3,[_4d,_4S,_Qb,_l2,_QF,_])),_QI=E(_OK),_QJ=jsQuerySelectorAll(E(_Qb),toJSStr(_QI)),_QK=B(_Q0(_QJ,_)),_QL=_Qc,_=_;while(1){var _QM=(function(_QN,_){var _QO=E(_QN);if(!_QO[0]){return _47;}else{var _QP=_QO[1],_QQ=_QO[2],_QR=rMV(_Pe),_QS=E(E(_QR)[7])[1],_QT=B(_Oq(_Q4,_QS));if(!_QT[0]){if(B(_NK(_QS,0))<3){var _QU=B(A(_l3,[_4d,_4S,_QP,_l2,_OO,_])),_QV=jsQuerySelectorAll(E(_QP),toJSStr(E(_ON))),_QW=B(_PM(_QV,_));_QL=_QQ;return null;}else{var _QX=B(A(_l3,[_4d,_4S,_QP,_l2,_OM,_]));_QL=_QQ;return null;}}else{var _QY=_QT[1],_QZ=new T(function(){var _R0=new T(function(){return B(_v(B(_H(0,E(_QY),_11)),_OI));},1);return B(_v(_OL,_R0));}),_R1=B(A(_l3,[_4d,_4S,_QP,_l2,_QZ,_])),_R2=jsQuerySelectorAll(E(_QP),toJSStr(_QI)),_R3=B(_Q0(_R2,_));_QL=_QQ;return null;}}})(_QL,_);if(_QM!=null){return _QM;}}}}})(_Q7,_);if(_Q8!=null){return _Q8;}}},_R4=B(_Q6(_PB,_)),_R5=function(_R6,_){while(1){var _R7=(function(_R8,_){var _R9=E(_R8);if(!_R9[0]){return _47;}else{var _Ra=_R9[1],_Rb=new T(function(){return B(_v(E(_Ra)[1],_OJ));}),_Rc=jsQuerySelectorAll(_Pz,toJSStr(B(unAppCStr("#character-detail-",_Rb)))),_Rd=function(_){var _Re=rMV(_Pe),_Rf=E(_Re),_Rg=_Rf[7],_Rh=new T(function(){var _Ri=E(_Rg),_Rj=_Ri[1],_Rk=new T(function(){return B(_v(_Rj,[1,_Ra,_11]));});return [0,_Rk,_Ri[2],_Ri[3],_Ri[4],_Ri[5]];}),_=wMV(_Pe,[0,_Rf[1],_Rf[2],_Rf[3],_Rf[4],_Rf[5],_Rf[6],_Rh]);return new F(function(){return _Pd(_Pe,_);});},_Rl=function(_Rm,_){return new F(function(){return _Rd(_);});},_Rn=function(_Ro,_){while(1){var _Rp=E(_Ro);if(!_Rp[0]){return _47;}else{var _Rq=B(A(_yE,[_4T,_4d,_46,_Rp[1],_w4,_Rl,_]));_Ro=_Rp[2];continue;}}},_Rr=function(_){var _Rs=rMV(_Pe),_Rt=E(_Rs),_Ru=_Rt[7],_Rv=new T(function(){var _Rw=E(_Ru),_Rx=_Rw[1],_Ry=new T(function(){return B(_Of(_NH,_Ra,_Rx));});return [0,_Ry,_Rw[2],_Rw[3],_Rw[4],_Rw[5]];}),_=wMV(_Pe,[0,_Rt[1],_Rt[2],_Rt[3],_Rt[4],_Rt[5],_Rt[6],_Rv]);return new F(function(){return _Pd(_Pe,_);});},_Rz=function(_RA,_){return new F(function(){return _Rr(_);});},_RB=function(_RC,_){while(1){var _RD=E(_RC);if(!_RD[0]){return _47;}else{var _RE=B(A(_yE,[_4T,_4d,_46,_RD[1],_w4,_Rz,_]));_RC=_RD[2];continue;}}},_RF=function(_sH){return new F(function(){return _NH(_Ra,_sH);});},_RG=function(_RH,_){while(1){var _RI=(function(_RJ,_){var _RK=E(_RJ);if(!_RK[0]){return _47;}else{var _RL=_RK[1],_RM=_RK[2],_RN=rMV(_Pe),_RO=E(E(_RN)[7])[1],_RP=B(_Oq(_RF,_RO));if(!_RP[0]){if(B(_NK(_RO,0))<3){var _RQ=B(A(_l3,[_4d,_4S,_RL,_l2,_OO,_])),_RR=E(_ON),_RS=jsQuerySelectorAll(E(_RL),toJSStr(_RR)),_RT=B(_Rn(_RS,_)),_RU=_RM,_=_;while(1){var _RV=(function(_RW,_){var _RX=E(_RW);if(!_RX[0]){return _47;}else{var _RY=_RX[1],_RZ=_RX[2],_S0=rMV(_Pe),_S1=E(E(_S0)[7])[1],_S2=B(_Oq(_RF,_S1));if(!_S2[0]){if(B(_NK(_S1,0))<3){var _S3=B(A(_l3,[_4d,_4S,_RY,_l2,_OO,_])),_S4=jsQuerySelectorAll(E(_RY),toJSStr(_RR)),_S5=B(_Rn(_S4,_));_RU=_RZ;return null;}else{var _S6=B(A(_l3,[_4d,_4S,_RY,_l2,_OM,_]));_RU=_RZ;return null;}}else{var _S7=_S2[1],_S8=new T(function(){var _S9=new T(function(){return B(_v(B(_H(0,E(_S7),_11)),_OI));},1);return B(_v(_OL,_S9));}),_Sa=B(A(_l3,[_4d,_4S,_RY,_l2,_S8,_])),_Sb=jsQuerySelectorAll(E(_RY),toJSStr(E(_OK))),_Sc=B(_RB(_Sb,_));_RU=_RZ;return null;}}})(_RU,_);if(_RV!=null){return _RV;}}}else{var _Sd=B(A(_l3,[_4d,_4S,_RL,_l2,_OM,_]));_RH=_RM;return null;}}else{var _Se=_RP[1],_Sf=new T(function(){var _Sg=new T(function(){return B(_v(B(_H(0,E(_Se),_11)),_OI));},1);return B(_v(_OL,_Sg));}),_Sh=B(A(_l3,[_4d,_4S,_RL,_l2,_Sf,_])),_Si=E(_OK),_Sj=jsQuerySelectorAll(E(_RL),toJSStr(_Si)),_Sk=B(_RB(_Sj,_)),_Sl=_RM,_=_;while(1){var _Sm=(function(_Sn,_){var _So=E(_Sn);if(!_So[0]){return _47;}else{var _Sp=_So[1],_Sq=_So[2],_Sr=rMV(_Pe),_Ss=E(E(_Sr)[7])[1],_St=B(_Oq(_RF,_Ss));if(!_St[0]){if(B(_NK(_Ss,0))<3){var _Su=B(A(_l3,[_4d,_4S,_Sp,_l2,_OO,_])),_Sv=jsQuerySelectorAll(E(_Sp),toJSStr(E(_ON))),_Sw=B(_Rn(_Sv,_));_Sl=_Sq;return null;}else{var _Sx=B(A(_l3,[_4d,_4S,_Sp,_l2,_OM,_]));_Sl=_Sq;return null;}}else{var _Sy=_St[1],_Sz=new T(function(){var _SA=new T(function(){return B(_v(B(_H(0,E(_Sy),_11)),_OI));},1);return B(_v(_OL,_SA));}),_SB=B(A(_l3,[_4d,_4S,_Sp,_l2,_Sz,_])),_SC=jsQuerySelectorAll(E(_Sp),toJSStr(_Si)),_SD=B(_RB(_SC,_));_Sl=_Sq;return null;}}})(_Sl,_);if(_Sm!=null){return _Sm;}}}}})(_RH,_);if(_RI!=null){return _RI;}}},_SE=B(_RG(_Rc,_));_R6=_R9[2];return null;}})(_R6,_);if(_R7!=null){return _R7;}}},_SF=_Pc,_SG=_P8,_=_,_SH=new T(function(){return B(_v(_SF,_OJ));}),_SI=jsQuerySelectorAll(_Pz,toJSStr(B(unAppCStr("#character-detail-",_SH)))),_SJ=function(_){var _SK=rMV(_Pe),_SL=E(_SK),_SM=_SL[7],_SN=new T(function(){var _SO=E(_SM),_SP=_SO[1],_SQ=new T(function(){return B(_v(_SP,[1,[0,_SF,_OF,_OE,_Op,_OG,_Oc,_On,_Od,_Oe,_Oe,_Oo,_Oo,_Ob],_11]));});return [0,_SQ,_SO[2],_SO[3],_SO[4],_SO[5]];}),_=wMV(_Pe,[0,_SL[1],_SL[2],_SL[3],_SL[4],_SL[5],_SL[6],_SN]);return new F(function(){return _Pd(_Pe,_);});},_SR=function(_SS,_){return new F(function(){return _SJ(_);});},_ST=function(_SU,_){while(1){var _SV=E(_SU);if(!_SV[0]){return _47;}else{var _SW=B(A(_yE,[_4T,_4d,_46,_SV[1],_w4,_SR,_]));_SU=_SV[2];continue;}}},_SX=function(_){var _SY=rMV(_Pe),_SZ=E(_SY),_T0=_SZ[7],_T1=new T(function(){var _T2=E(_T0),_T3=_T2[1],_T4=new T(function(){return B(_Of(_NH,[0,_SF,_OF,_OE,_Op,_OG,_Oc,_On,_Od,_Oe,_Oe,_Oo,_Oo,_Ob],_T3));});return [0,_T4,_T2[2],_T2[3],_T2[4],_T2[5]];}),_=wMV(_Pe,[0,_SZ[1],_SZ[2],_SZ[3],_SZ[4],_SZ[5],_SZ[6],_T1]);return new F(function(){return _Pd(_Pe,_);});},_T5=function(_T6,_){return new F(function(){return _SX(_);});},_T7=function(_T8,_){while(1){var _T9=E(_T8);if(!_T9[0]){return _47;}else{var _Ta=B(A(_yE,[_4T,_4d,_46,_T9[1],_w4,_T5,_]));_T8=_T9[2];continue;}}},_Tb=function(_Tc){return new F(function(){return _NC(_SF,E(_Tc)[1]);});},_Td=function(_Te,_){while(1){var _Tf=(function(_Tg,_){var _Th=E(_Tg);if(!_Th[0]){return _47;}else{var _Ti=_Th[1],_Tj=_Th[2],_Tk=rMV(_Pe),_Tl=E(E(_Tk)[7])[1],_Tm=B(_Oq(_Tb,_Tl));if(!_Tm[0]){if(B(_NK(_Tl,0))<3){var _Tn=B(A(_l3,[_4d,_4S,_Ti,_l2,_OO,_])),_To=E(_ON),_Tp=jsQuerySelectorAll(E(_Ti),toJSStr(_To)),_Tq=B(_ST(_Tp,_)),_Tr=_Tj,_=_;while(1){var _Ts=(function(_Tt,_){var _Tu=E(_Tt);if(!_Tu[0]){return _47;}else{var _Tv=_Tu[1],_Tw=_Tu[2],_Tx=rMV(_Pe),_Ty=E(E(_Tx)[7])[1],_Tz=B(_Oq(_Tb,_Ty));if(!_Tz[0]){if(B(_NK(_Ty,0))<3){var _TA=B(A(_l3,[_4d,_4S,_Tv,_l2,_OO,_])),_TB=jsQuerySelectorAll(E(_Tv),toJSStr(_To)),_TC=B(_ST(_TB,_));_Tr=_Tw;return null;}else{var _TD=B(A(_l3,[_4d,_4S,_Tv,_l2,_OM,_]));_Tr=_Tw;return null;}}else{var _TE=_Tz[1],_TF=new T(function(){var _TG=new T(function(){return B(_v(B(_H(0,E(_TE),_11)),_OI));},1);return B(_v(_OL,_TG));}),_TH=B(A(_l3,[_4d,_4S,_Tv,_l2,_TF,_])),_TI=jsQuerySelectorAll(E(_Tv),toJSStr(E(_OK))),_TJ=B(_T7(_TI,_));_Tr=_Tw;return null;}}})(_Tr,_);if(_Ts!=null){return _Ts;}}}else{var _TK=B(A(_l3,[_4d,_4S,_Ti,_l2,_OM,_]));_Te=_Tj;return null;}}else{var _TL=_Tm[1],_TM=new T(function(){var _TN=new T(function(){return B(_v(B(_H(0,E(_TL),_11)),_OI));},1);return B(_v(_OL,_TN));}),_TO=B(A(_l3,[_4d,_4S,_Ti,_l2,_TM,_])),_TP=E(_OK),_TQ=jsQuerySelectorAll(E(_Ti),toJSStr(_TP)),_TR=B(_T7(_TQ,_)),_TS=_Tj,_=_;while(1){var _TT=(function(_TU,_){var _TV=E(_TU);if(!_TV[0]){return _47;}else{var _TW=_TV[1],_TX=_TV[2],_TY=rMV(_Pe),_TZ=E(E(_TY)[7])[1],_U0=B(_Oq(_Tb,_TZ));if(!_U0[0]){if(B(_NK(_TZ,0))<3){var _U1=B(A(_l3,[_4d,_4S,_TW,_l2,_OO,_])),_U2=jsQuerySelectorAll(E(_TW),toJSStr(E(_ON))),_U3=B(_ST(_U2,_));_TS=_TX;return null;}else{var _U4=B(A(_l3,[_4d,_4S,_TW,_l2,_OM,_]));_TS=_TX;return null;}}else{var _U5=_U0[1],_U6=new T(function(){var _U7=new T(function(){return B(_v(B(_H(0,E(_U5),_11)),_OI));},1);return B(_v(_OL,_U7));}),_U8=B(A(_l3,[_4d,_4S,_TW,_l2,_U6,_])),_U9=jsQuerySelectorAll(E(_TW),toJSStr(_TP)),_Ua=B(_T7(_U9,_));_TS=_TX;return null;}}})(_TS,_);if(_TT!=null){return _TT;}}}}})(_Te,_);if(_Tf!=null){return _Tf;}}},_Ub=B(_Td(_SI,_));return new F(function(){return _R5(_SG,_);});}}},_Uc=function(_Ud,_Ue){while(1){var _Uf=E(_Ud);if(!_Uf[0]){return (E(_Ue)[0]==0)?true:false;}else{var _Ug=E(_Ue);if(!_Ug[0]){return false;}else{if(E(_Uf[1])!=E(_Ug[1])){return false;}else{_Ud=_Uf[2];_Ue=_Ug[2];continue;}}}}},_Uh=function(_Ui,_Uj){return (!B(_Uc(_Ui,_Uj)))?true:false;},_Uk=[0,_Uc,_Uh],_Ul=function(_Um,_Un){return (B(_5u(_Um,_Un))==0)?true:false;},_Uo=function(_Up,_Uq){return (B(_5u(_Up,_Uq))==2)?false:true;},_Ur=function(_Us,_Ut){return (B(_5u(_Us,_Ut))==2)?true:false;},_Uu=function(_Uv,_Uw){return (B(_5u(_Uv,_Uw))==0)?false:true;},_Ux=function(_Uy,_Uz){return (B(_5u(_Uy,_Uz))==2)?E(_Uy):E(_Uz);},_UA=function(_UB,_UC){return (B(_5u(_UB,_UC))==2)?E(_UC):E(_UB);},_UD=[0,_Uk,_5u,_Ul,_Uo,_Ur,_Uu,_Ux,_UA],_UE=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:185:21-27"));}),_UF=[0,_3c,_3d,_11,_UE,_3c,_3c],_UG=new T(function(){return B(_3a(_UF));}),_UH=function(_){return new F(function(){return die(_UG);});},_UI=true,_UJ=function(_){return _47;},_UK=new T(function(){return B(unCStr("Map.!: given key is not an element in the map"));}),_UL=new T(function(){return B(err(_UK));}),_UM=function(_UN,_UO,_UP){var _UQ=_UO,_UR=_UP;while(1){var _US=E(_UQ),_UT=E(_UR);if(!_UT[0]){switch(B(A(_xd,[_UN,_US,_UT[2]]))){case 0:_UQ=_US;_UR=_UT[4];continue;case 1:return E(_UT[3]);default:_UQ=_US;_UR=_UT[5];continue;}}else{return E(_UL);}}},_UU=function(_UV,_UW,_UX,_UY){var _UZ=function(_){return new F(function(){return jsGetAttr(B(A(_km,[_UV,_UX])),E(_UY));});};return new F(function(){return A(_ko,[_UW,_UZ]);});},_V0=function(_V1,_V2,_V3,_V4){var _V5=B(_nD(_V2)),_V6=new T(function(){return B(_nP(_V5));}),_V7=function(_V8){var _V9=new T(function(){return B(_nH(_V8));});return new F(function(){return A(_V6,[_V9]);});},_Va=new T(function(){var _Vb=new T(function(){return toJSStr(E(_V4));});return B(_UU(_V1,_V2,_V3,_Vb));});return new F(function(){return A(_nF,[_V5,_Va,_V7]);});},_Vc="value",_Vd=new T(function(){return B(unCStr("tactic-detail-table"));}),_Ve=[1,_lA,_Vd],_Vf=new T(function(){return B(unCStr("edit-tactic-done"));}),_Vg=[1,_lA,_Vf],_Vh=new T(function(){return B(unCStr("tactic-detail"));}),_Vi=[1,_lA,_Vh],_Vj=new T(function(){return B(unCStr("tactic-list-tbody"));}),_Vk=[1,_lA,_Vj],_Vl=new T(function(){return B(unCStr("id"));}),_Vm=function(_Vn,_Vo){return E(_Vn)!=E(_Vo);},_Vp=function(_Vq,_Vr){return E(_Vq)==E(_Vr);},_Vs=[0,_Vp,_Vm],_Vt=new T(function(){return B(unCStr("-"));}),_Vu=function(_Vv){return E(E(_Vv)[1]);},_Vw=2,_Vx=[1,_11],_Vy=[1,_Vx,_11],_Vz=function(_VA){while(1){var _VB=(function(_VC){var _VD=E(_VC);if(!_VD[0]){return [0];}else{var _VE=_VD[2],_VF=E(_VD[1]);if(!_VF[0]){_VA=_VE;return null;}else{var _VG=new T(function(){return B(_Vz(_VE));});return [1,_VF,_VG];}}})(_VA);if(_VB!=null){return _VB;}}},_VH=function(_VI){var _VJ=E(_VI);return (_VJ[0]==0)?E(_VJ[1]):E(_VJ[1]);},_VK=1,_VL=function(_VM,_VN){var _VO=E(_VN);if(!_VO[0]){return [0];}else{var _VP=_VO[1],_VQ=_VO[2],_VR=function(_VS){var _VT=E(_VP);if(!_VT[0]){var _VU=E(_VQ);if(!_VU[0]){return [1,_VT,_Vy];}else{if(!E(_VU[1])[0]){var _VV=new T(function(){return B(_VL(_VM,_VU));});return [1,_VT,[1,_Vx,_VV]];}else{var _VW=new T(function(){return B(_VL(_VM,_VU));});return [1,_VT,_VW];}}}else{var _VX=new T(function(){return B(_VL(_VM,_VQ));});return [1,_VT,_VX];}};if(E(_VM)==1){var _VY=E(_VP);if(!_VY[0]){var _VZ=E(_VQ);if(!_VZ[0]){return new F(function(){return _VR(_);});}else{if(!E(_VZ[1])[0]){var _W0=new T(function(){return B(_VL(_VK,_VZ));});return [1,_VY,_W0];}else{return new F(function(){return _VR(_);});}}}else{return new F(function(){return _VR(_);});}}else{return new F(function(){return _VR(_);});}}},_W1=function(_W2,_W3){var _W4=E(_W2);if(!_W4[0]){return [1,[0,_11,_W3]];}else{var _W5=E(_W3);if(!_W5[0]){return [0];}else{var _W6=_W5[1];if(!B(A(_W4[1],[_W6]))){return [0];}else{var _W7=B(_W1(_W4[2],_W5[2]));if(!_W7[0]){return [0];}else{var _W8=E(_W7[1]);return [1,[0,[1,_W6,_W8[1]],_W8[2]]];}}}}},_W9=function(_Wa,_Wb){var _Wc=E(_Wa);if(!_Wc[0]){return [0,_11,[1,[0,_11,_Wb]]];}else{var _Wd=E(_Wb);if(!_Wd[0]){return [0,_11,_3c];}else{var _We=_Wd[2],_Wf=B(_W1(_Wc,_Wd));if(!_Wf[0]){var _Wg=new T(function(){var _Wh=B(_W9(_Wc,_We));return [0,_Wh[1],_Wh[2]];}),_Wi=new T(function(){return E(E(_Wg)[2]);}),_Wj=new T(function(){return E(E(_Wg)[1]);});return [0,[1,_Wd[1],_Wj],_Wi];}else{return [0,_11,_Wf];}}}},_Wk=[0,_11],_Wl=function(_Wm,_Wn){var _Wo=E(_Wn);if(!_Wo[0]){return [0];}else{var _Wp=B(_W9(_Wm,_Wo)),_Wq=_Wp[2],_Wr=function(_Ws){var _Wt=E(_Ws);if(!_Wt[0]){return [0];}else{var _Wu=E(_Wt[1]),_Wv=_Wu[2],_Ww=E(_Wu[1]);if(!_Ww[0]){var _Wx=E(_Wv);if(!_Wx[0]){var _Wy=new T(function(){return B(_Wl(_Wm,_11));});return [1,_Wk,_Wy];}else{var _Wz=_Wx[2],_WA=new T(function(){return B(_Wl(_Wm,_Wz));});return [1,_Wk,[1,[1,[1,_Wx[1],_11]],_WA]];}}else{var _WB=new T(function(){return B(_Wl(_Wm,_Wv));});return [1,[0,_Ww],_WB];}}},_WC=E(_Wp[1]);if(!_WC[0]){return new F(function(){return _Wr(_Wq);});}else{var _WD=new T(function(){return B(_Wr(_Wq));});return [1,[1,_WC],_WD];}}},_WE=function(_WF,_WG){var _WH=new T(function(){var _WI=new T(function(){return B(_Vu(_WF));});return B(_wI(_WI,_WG));}),_WJ=function(_WK){var _WL=B(_Wl(_WH,_WK));if(!_WL[0]){var _WM=B(_Vz(_Vy));if(!_WM[0]){return new F(function(){return _wI(_VH,_11);});}else{return new F(function(){return _wI(_VH,_WM);});}}else{if(!E(_WL[1])[0]){var _WN=new T(function(){return B(_VL(_Vw,_WL));}),_WO=B(_Vz([1,_Vx,_WN]));if(!_WO[0]){return new F(function(){return _wI(_VH,_11);});}else{return new F(function(){return _wI(_VH,_WO);});}}else{var _WP=B(_Vz(B(_VL(_Vw,_WL))));if(!_WP[0]){return new F(function(){return _wI(_VH,_11);});}else{return new F(function(){return _wI(_VH,_WP);});}}}};return E(_WJ);},_WQ=new T(function(){return B(_WE(_Vs,_Vt));}),_WR=new T(function(){return B(unCStr(".selectpicker"));}),_WS=new T(function(){return B(unCStr("Prelude.read: no parse"));}),_WT=new T(function(){return B(err(_WS));}),_WU=new T(function(){return B(unCStr("Prelude.read: ambiguous parse"));}),_WV=new T(function(){return B(err(_WU));}),_WW=new T(function(){return B(_mW("Text/ParserCombinators/ReadP.hs:(128,3)-(151,52)|function <|>"));}),_WX=function(_WY,_WZ){while(1){var _X0=(function(_X1,_X2){var _X3=E(_X1);switch(_X3[0]){case 0:var _X4=E(_X2);if(!_X4[0]){return [0];}else{_WY=B(A(_X3[1],[_X4[1]]));_WZ=_X4[2];return null;}break;case 1:var _X5=B(A(_X3[1],[_X2])),_X6=_X2;_WY=_X5;_WZ=_X6;return null;case 2:return [0];case 3:var _X7=_X3[2],_X8=new T(function(){return B(_WX(_X7,_X2));});return [1,[0,_X3[1],_X2],_X8];default:return E(_X3[1]);}})(_WY,_WZ);if(_X0!=null){return _X0;}}},_X9=function(_Xa,_Xb){var _Xc=function(_Xd){var _Xe=E(_Xb);if(_Xe[0]==3){var _Xf=_Xe[2],_Xg=new T(function(){return B(_X9(_Xa,_Xf));});return [3,_Xe[1],_Xg];}else{var _Xh=E(_Xa);if(_Xh[0]==2){return E(_Xe);}else{var _Xi=E(_Xe);if(_Xi[0]==2){return E(_Xh);}else{var _Xj=function(_Xk){var _Xl=E(_Xi);if(_Xl[0]==4){var _Xm=_Xl[1];return [1,function(_Xn){return [4,new T(function(){return B(_v(B(_WX(_Xh,_Xn)),_Xm));})];}];}else{var _Xo=E(_Xh);if(_Xo[0]==1){var _Xp=_Xo[1],_Xq=E(_Xl);if(!_Xq[0]){return [1,function(_Xr){return new F(function(){return _X9(B(A(_Xp,[_Xr])),_Xq);});}];}else{var _Xs=_Xq[1];return [1,function(_Xt){var _Xu=new T(function(){return B(A(_Xs,[_Xt]));});return new F(function(){return _X9(B(A(_Xp,[_Xt])),_Xu);});}];}}else{var _Xv=E(_Xl);if(!_Xv[0]){return E(_WW);}else{var _Xw=_Xv[1];return [1,function(_Xx){var _Xy=new T(function(){return B(A(_Xw,[_Xx]));});return new F(function(){return _X9(_Xo,_Xy);});}];}}}},_Xz=E(_Xh);switch(_Xz[0]){case 1:var _XA=_Xz[1],_XB=E(_Xi);if(_XB[0]==4){var _XC=_XB[1];return [1,function(_XD){return [4,new T(function(){return B(_v(B(_WX(B(A(_XA,[_XD])),_XD)),_XC));})];}];}else{return new F(function(){return _Xj(_);});}break;case 4:var _XE=_Xz[1],_XF=E(_Xi);switch(_XF[0]){case 0:return [1,function(_XG){return [4,new T(function(){var _XH=new T(function(){return B(_WX(_XF,_XG));},1);return B(_v(_XE,_XH));})];}];case 1:var _XI=_XF[1];return [1,function(_XJ){return [4,new T(function(){var _XK=new T(function(){return B(_WX(B(A(_XI,[_XJ])),_XJ));},1);return B(_v(_XE,_XK));})];}];default:var _XL=_XF[1];return [4,new T(function(){return B(_v(_XE,_XL));})];}break;default:return new F(function(){return _Xj(_);});}}}}},_XM=E(_Xa);switch(_XM[0]){case 0:var _XN=_XM[1],_XO=E(_Xb);if(!_XO[0]){var _XP=_XO[1];return [0,function(_XQ){var _XR=new T(function(){return B(A(_XP,[_XQ]));});return new F(function(){return _X9(B(A(_XN,[_XQ])),_XR);});}];}else{return new F(function(){return _Xc(_);});}break;case 3:var _XS=_XM[2],_XT=new T(function(){return B(_X9(_XS,_Xb));});return [3,_XM[1],_XT];default:return new F(function(){return _Xc(_);});}},_XU=new T(function(){return B(unCStr("("));}),_XV=new T(function(){return B(unCStr(")"));}),_XW=function(_XX,_XY){var _XZ=E(_XX);switch(_XZ[0]){case 0:var _Y0=_XZ[1];return [0,function(_Y1){return new F(function(){return _XW(B(A(_Y0,[_Y1])),_XY);});}];case 1:var _Y2=_XZ[1];return [1,function(_Y3){return new F(function(){return _XW(B(A(_Y2,[_Y3])),_XY);});}];case 2:return [2];case 3:var _Y4=_XZ[2],_Y5=new T(function(){return B(_XW(_Y4,_XY));});return new F(function(){return _X9(B(A(_XY,[_XZ[1]])),_Y5);});break;default:var _Y6=function(_Y7){var _Y8=E(_Y7);if(!_Y8[0]){return [0];}else{var _Y9=_Y8[2],_Ya=E(_Y8[1]),_Yb=new T(function(){return B(_Y6(_Y9));},1);return new F(function(){return _v(B(_WX(B(A(_XY,[_Ya[1]])),_Ya[2])),_Yb);});}},_Yc=B(_Y6(_XZ[1]));return (_Yc[0]==0)?[2]:[4,_Yc];}},_Yd=[2],_Ye=function(_Yf){return [3,_Yf,_Yd];},_Yg=function(_Yh,_Yi){var _Yj=E(_Yh);if(!_Yj){return new F(function(){return A(_Yi,[_47]);});}else{var _Yk=new T(function(){return B(_Yg(_Yj-1|0,_Yi));});return [0,function(_Yl){return E(_Yk);}];}},_Ym=function(_Yn,_Yo,_Yp){var _Yq=new T(function(){return B(A(_Yn,[_Ye]));}),_Yr=function(_Ys,_Yt,_Yu,_Yv){while(1){var _Yw=(function(_Yx,_Yy,_Yz,_YA){var _YB=E(_Yx);switch(_YB[0]){case 0:var _YC=E(_Yy);if(!_YC[0]){return new F(function(){return A(_Yo,[_YA]);});}else{_Ys=B(A(_YB[1],[_YC[1]]));_Yt=_YC[2];var _YD=_Yz+1|0,_YE=_YA;_Yu=_YD;_Yv=_YE;return null;}break;case 1:var _YF=B(A(_YB[1],[_Yy])),_YG=_Yy,_YD=_Yz,_YE=_YA;_Ys=_YF;_Yt=_YG;_Yu=_YD;_Yv=_YE;return null;case 2:return new F(function(){return A(_Yo,[_YA]);});break;case 3:var _YH=new T(function(){return B(_XW(_YB,_YA));}),_YI=function(_YJ){return E(_YH);};return new F(function(){return _Yg(_Yz,_YI);});break;default:return new F(function(){return _XW(_YB,_YA);});}})(_Ys,_Yt,_Yu,_Yv);if(_Yw!=null){return _Yw;}}};return function(_YK){return new F(function(){return _Yr(_Yq,_YK,0,_Yp);});};},_YL=function(_YM){return new F(function(){return A(_YM,[_11]);});},_YN=function(_YO,_YP){var _YQ=function(_YR){var _YS=E(_YR);if(!_YS[0]){return E(_YL);}else{var _YT=_YS[1],_YU=_YS[2];if(!B(A(_YO,[_YT]))){return E(_YL);}else{var _YV=new T(function(){return B(_YQ(_YU));}),_YW=function(_YX){var _YY=new T(function(){var _YZ=function(_Z0){return new F(function(){return A(_YX,[[1,_YT,_Z0]]);});};return B(A(_YV,[_YZ]));});return [0,function(_Z1){return E(_YY);}];};return E(_YW);}}};return function(_Z2){return new F(function(){return A(_YQ,[_Z2,_YP]);});};},_Z3=[6],_Z4=new T(function(){return B(unCStr("valDig: Bad base"));}),_Z5=new T(function(){return B(err(_Z4));}),_Z6=function(_Z7,_Z8){var _Z9=function(_Za,_Zb){var _Zc=E(_Za);if(!_Zc[0]){var _Zd=new T(function(){return B(A(_Zb,[_11]));}),_Ze=function(_Zf){return new F(function(){return A(_Zf,[_Zd]);});};return E(_Ze);}else{var _Zg=_Zc[2],_Zh=E(_Zc[1]),_Zi=function(_Zj){var _Zk=new T(function(){var _Zl=function(_Zm){return new F(function(){return A(_Zb,[[1,_Zj,_Zm]]);});};return B(_Z9(_Zg,_Zl));}),_Zn=function(_Zo){var _Zp=new T(function(){return B(A(_Zk,[_Zo]));});return [0,function(_Zq){return E(_Zp);}];};return E(_Zn);};switch(E(_Z7)){case 8:if(48>_Zh){var _Zr=new T(function(){return B(A(_Zb,[_11]));}),_Zs=function(_Zt){return new F(function(){return A(_Zt,[_Zr]);});};return E(_Zs);}else{if(_Zh>55){var _Zu=new T(function(){return B(A(_Zb,[_11]));}),_Zv=function(_Zw){return new F(function(){return A(_Zw,[_Zu]);});};return E(_Zv);}else{return new F(function(){return _Zi(_Zh-48|0);});}}break;case 10:if(48>_Zh){var _Zx=new T(function(){return B(A(_Zb,[_11]));}),_Zy=function(_Zz){return new F(function(){return A(_Zz,[_Zx]);});};return E(_Zy);}else{if(_Zh>57){var _ZA=new T(function(){return B(A(_Zb,[_11]));}),_ZB=function(_ZC){return new F(function(){return A(_ZC,[_ZA]);});};return E(_ZB);}else{return new F(function(){return _Zi(_Zh-48|0);});}}break;case 16:if(48>_Zh){if(97>_Zh){if(65>_Zh){var _ZD=new T(function(){return B(A(_Zb,[_11]));}),_ZE=function(_ZF){return new F(function(){return A(_ZF,[_ZD]);});};return E(_ZE);}else{if(_Zh>70){var _ZG=new T(function(){return B(A(_Zb,[_11]));}),_ZH=function(_ZI){return new F(function(){return A(_ZI,[_ZG]);});};return E(_ZH);}else{return new F(function(){return _Zi((_Zh-65|0)+10|0);});}}}else{if(_Zh>102){if(65>_Zh){var _ZJ=new T(function(){return B(A(_Zb,[_11]));}),_ZK=function(_ZL){return new F(function(){return A(_ZL,[_ZJ]);});};return E(_ZK);}else{if(_Zh>70){var _ZM=new T(function(){return B(A(_Zb,[_11]));}),_ZN=function(_ZO){return new F(function(){return A(_ZO,[_ZM]);});};return E(_ZN);}else{return new F(function(){return _Zi((_Zh-65|0)+10|0);});}}}else{return new F(function(){return _Zi((_Zh-97|0)+10|0);});}}}else{if(_Zh>57){if(97>_Zh){if(65>_Zh){var _ZP=new T(function(){return B(A(_Zb,[_11]));}),_ZQ=function(_ZR){return new F(function(){return A(_ZR,[_ZP]);});};return E(_ZQ);}else{if(_Zh>70){var _ZS=new T(function(){return B(A(_Zb,[_11]));}),_ZT=function(_ZU){return new F(function(){return A(_ZU,[_ZS]);});};return E(_ZT);}else{return new F(function(){return _Zi((_Zh-65|0)+10|0);});}}}else{if(_Zh>102){if(65>_Zh){var _ZV=new T(function(){return B(A(_Zb,[_11]));}),_ZW=function(_ZX){return new F(function(){return A(_ZX,[_ZV]);});};return E(_ZW);}else{if(_Zh>70){var _ZY=new T(function(){return B(A(_Zb,[_11]));}),_ZZ=function(_100){return new F(function(){return A(_100,[_ZY]);});};return E(_ZZ);}else{return new F(function(){return _Zi((_Zh-65|0)+10|0);});}}}else{return new F(function(){return _Zi((_Zh-97|0)+10|0);});}}}else{return new F(function(){return _Zi(_Zh-48|0);});}}break;default:return E(_Z5);}}},_101=function(_102){var _103=E(_102);if(!_103[0]){return [2];}else{return new F(function(){return A(_Z8,[_103]);});}};return function(_104){return new F(function(){return A(_Z9,[_104,_4b,_101]);});};},_105=function(_106){return new F(function(){return A(_106,[_3c]);});},_107=function(_108){return new F(function(){return A(_108,[_3c]);});},_109=10,_10a=function(_10b){var _10c=function(_10d){return new F(function(){return A(_10b,[[1,_10d]]);});};return function(_10e){return (E(_10e)==46)?[1,B(_Z6(_109,_10c))]:[2];};},_10f=function(_10g){return [0,B(_10a(_10g))];},_10h=[0,1],_10i=[0,2147483647],_10j=function(_10k,_10l){while(1){var _10m=E(_10k);if(!_10m[0]){var _10n=_10m[1],_10o=E(_10l);if(!_10o[0]){var _10p=_10o[1],_10q=addC(_10n,_10p);if(!E(_10q[2])){return [0,_10q[1]];}else{_10k=[1,I_fromInt(_10n)];_10l=[1,I_fromInt(_10p)];continue;}}else{_10k=[1,I_fromInt(_10n)];_10l=_10o;continue;}}else{var _10r=E(_10l);if(!_10r[0]){_10k=_10m;_10l=[1,I_fromInt(_10r[1])];continue;}else{return [1,I_add(_10m[1],_10r[1])];}}}},_10s=new T(function(){return B(_10j(_10i,_10h));}),_10t=function(_10u){var _10v=E(_10u);if(!_10v[0]){var _10w=E(_10v[1]);return (_10w==(-2147483648))?E(_10s):[0, -_10w];}else{return [1,I_negate(_10v[1])];}},_10x=[0,10],_10y=function(_10z){return [0,_10z];},_10A=function(_10B){return new F(function(){return _10y(E(_10B));});},_10C=new T(function(){return B(unCStr("this should not happen"));}),_10D=new T(function(){return B(err(_10C));}),_10E=function(_10F,_10G){while(1){var _10H=E(_10F);if(!_10H[0]){var _10I=_10H[1],_10J=E(_10G);if(!_10J[0]){var _10K=_10J[1];if(!(imul(_10I,_10K)|0)){return [0,imul(_10I,_10K)|0];}else{_10F=[1,I_fromInt(_10I)];_10G=[1,I_fromInt(_10K)];continue;}}else{_10F=[1,I_fromInt(_10I)];_10G=_10J;continue;}}else{var _10L=E(_10G);if(!_10L[0]){_10F=_10H;_10G=[1,I_fromInt(_10L[1])];continue;}else{return [1,I_mul(_10H[1],_10L[1])];}}}},_10M=function(_10N,_10O){var _10P=E(_10O);if(!_10P[0]){return [0];}else{var _10Q=E(_10P[2]);if(!_10Q[0]){return E(_10D);}else{var _10R=_10Q[2],_10S=new T(function(){return B(_10M(_10N,_10R));});return [1,B(_10j(B(_10E(_10P[1],_10N)),_10Q[1])),_10S];}}},_10T=[0,0],_10U=function(_10V,_10W,_10X){while(1){var _10Y=(function(_10Z,_110,_111){var _112=E(_111);if(!_112[0]){return E(_10T);}else{if(!E(_112[2])[0]){return E(_112[1]);}else{var _113=E(_110);if(_113<=40){var _114=_10T,_115=_112;while(1){var _116=E(_115);if(!_116[0]){return E(_114);}else{var _117=B(_10j(B(_10E(_114,_10Z)),_116[1]));_115=_116[2];_114=_117;continue;}}}else{var _118=B(_10E(_10Z,_10Z));if(!(_113%2)){_10V=_118;_10W=quot(_113+1|0,2);var _119=B(_10M(_10Z,_112));_10X=_119;return null;}else{_10V=_118;_10W=quot(_113+1|0,2);var _119=B(_10M(_10Z,[1,_10T,_112]));_10X=_119;return null;}}}}})(_10V,_10W,_10X);if(_10Y!=null){return _10Y;}}},_11a=function(_11b,_11c){var _11d=new T(function(){return B(_NK(_11c,0));},1);return new F(function(){return _10U(_11b,_11d,B(_wI(_10A,_11c)));});},_11e=function(_11f){var _11g=new T(function(){var _11h=new T(function(){var _11i=function(_11j){var _11k=new T(function(){return B(_11a(_10x,_11j));});return new F(function(){return A(_11f,[[1,_11k]]);});};return [1,B(_Z6(_109,_11i))];}),_11l=function(_11m){if(E(_11m)==43){var _11n=function(_11o){var _11p=new T(function(){return B(_11a(_10x,_11o));});return new F(function(){return A(_11f,[[1,_11p]]);});};return [1,B(_Z6(_109,_11n))];}else{return [2];}},_11q=function(_11r){if(E(_11r)==45){var _11s=function(_11t){var _11u=new T(function(){return B(_10t(B(_11a(_10x,_11t))));});return new F(function(){return A(_11f,[[1,_11u]]);});};return [1,B(_Z6(_109,_11s))];}else{return [2];}};return B(_X9(B(_X9([0,_11q],[0,_11l])),_11h));}),_11v=function(_11w){return (E(_11w)==69)?E(_11g):[2];},_11x=function(_11y){return (E(_11y)==101)?E(_11g):[2];};return new F(function(){return _X9([0,_11x],[0,_11v]);});},_11z=function(_11A){var _11B=function(_11C){var _11D=function(_11E){var _11F=function(_11G){return new F(function(){return A(_11A,[[5,[1,_11C,_11E,_11G]]]);});};return [1,B(_Ym(_11e,_105,_11F))];};return [1,B(_Ym(_10f,_107,_11D))];};return new F(function(){return _Z6(_109,_11B);});},_11H=function(_11I){return [1,B(_11z(_11I))];},_11J=16,_11K=8,_11L=function(_11M){var _11N=function(_11O){return new F(function(){return A(_11M,[[5,[0,_11K,_11O]]]);});},_11P=function(_11Q){return new F(function(){return A(_11M,[[5,[0,_11J,_11Q]]]);});},_11R=function(_11S){switch(E(_11S)){case 79:return [1,B(_Z6(_11K,_11N))];case 88:return [1,B(_Z6(_11J,_11P))];case 111:return [1,B(_Z6(_11K,_11N))];case 120:return [1,B(_Z6(_11J,_11P))];default:return [2];}},_11T=[0,_11R];return function(_11U){return (E(_11U)==48)?E(_11T):[2];};},_11V=function(_11W){return [0,B(_11L(_11W))];},_11X=function(_11Y,_11Z,_120){while(1){var _121=E(_120);if(!_121[0]){return false;}else{if(!B(A(_Vu,[_11Y,_11Z,_121[1]]))){_120=_121[2];continue;}else{return true;}}}},_122=new T(function(){return B(unCStr("!@#$%&*+./<=>?\\^|:-~"));}),_123=function(_124){return new F(function(){return _11X(_Vs,_124,_122);});},_125=false,_126=function(_127){var _128=new T(function(){return B(A(_127,[_11K]));}),_129=new T(function(){return B(A(_127,[_11J]));});return function(_12a){switch(E(_12a)){case 79:return E(_128);case 88:return E(_129);case 111:return E(_128);case 120:return E(_129);default:return [2];}};},_12b=function(_12c){return [0,B(_126(_12c))];},_12d=function(_12e){return new F(function(){return A(_12e,[_109]);});},_12f=function(_12g){var _12h=new T(function(){return B(_H(9,_12g,_11));});return new F(function(){return err(B(unAppCStr("Prelude.chr: bad argument: ",_12h)));});},_12i=function(_12j){var _12k=E(_12j);if(!_12k[0]){return E(_12k[1]);}else{return new F(function(){return I_toInt(_12k[1]);});}},_12l=function(_12m,_12n){var _12o=E(_12m);if(!_12o[0]){var _12p=_12o[1],_12q=E(_12n);return (_12q[0]==0)?_12p<=_12q[1]:I_compareInt(_12q[1],_12p)>=0;}else{var _12r=_12o[1],_12s=E(_12n);return (_12s[0]==0)?I_compareInt(_12r,_12s[1])<=0:I_compare(_12r,_12s[1])<=0;}},_12t=function(_12u){return [2];},_12v=function(_12w){var _12x=E(_12w);if(!_12x[0]){return E(_12t);}else{var _12y=_12x[1],_12z=E(_12x[2]);if(!_12z[0]){return E(_12y);}else{var _12A=new T(function(){return B(_12v(_12z));}),_12B=function(_12C){var _12D=new T(function(){return B(A(_12A,[_12C]));});return new F(function(){return _X9(B(A(_12y,[_12C])),_12D);});};return E(_12B);}}},_12E=function(_12F,_12G){var _12H=function(_12I,_12J,_12K){var _12L=E(_12I);if(!_12L[0]){return new F(function(){return A(_12K,[_12F]);});}else{var _12M=_12L[2],_12N=E(_12J);if(!_12N[0]){return [2];}else{var _12O=_12N[2];if(E(_12L[1])!=E(_12N[1])){return [2];}else{var _12P=new T(function(){return B(_12H(_12M,_12O,_12K));});return [0,function(_12Q){return E(_12P);}];}}}};return function(_12R){return new F(function(){return _12H(_12F,_12R,_12G);});};},_12S=new T(function(){return B(unCStr("SO"));}),_12T=14,_12U=function(_12V){var _12W=new T(function(){return B(A(_12V,[_12T]));}),_12X=function(_12Y){return E(_12W);};return [1,B(_12E(_12S,_12X))];},_12Z=new T(function(){return B(unCStr("SOH"));}),_130=1,_131=function(_132){var _133=new T(function(){return B(A(_132,[_130]));}),_134=function(_135){return E(_133);};return [1,B(_12E(_12Z,_134))];},_136=function(_137){return [1,B(_Ym(_131,_12U,_137))];},_138=new T(function(){return B(unCStr("NUL"));}),_139=0,_13a=function(_13b){var _13c=new T(function(){return B(A(_13b,[_139]));}),_13d=function(_13e){return E(_13c);};return [1,B(_12E(_138,_13d))];},_13f=new T(function(){return B(unCStr("STX"));}),_13g=2,_13h=function(_13i){var _13j=new T(function(){return B(A(_13i,[_13g]));}),_13k=function(_13l){return E(_13j);};return [1,B(_12E(_13f,_13k))];},_13m=new T(function(){return B(unCStr("ETX"));}),_13n=3,_13o=function(_13p){var _13q=new T(function(){return B(A(_13p,[_13n]));}),_13r=function(_13s){return E(_13q);};return [1,B(_12E(_13m,_13r))];},_13t=new T(function(){return B(unCStr("EOT"));}),_13u=4,_13v=function(_13w){var _13x=new T(function(){return B(A(_13w,[_13u]));}),_13y=function(_13z){return E(_13x);};return [1,B(_12E(_13t,_13y))];},_13A=new T(function(){return B(unCStr("ENQ"));}),_13B=5,_13C=function(_13D){var _13E=new T(function(){return B(A(_13D,[_13B]));}),_13F=function(_13G){return E(_13E);};return [1,B(_12E(_13A,_13F))];},_13H=new T(function(){return B(unCStr("ACK"));}),_13I=6,_13J=function(_13K){var _13L=new T(function(){return B(A(_13K,[_13I]));}),_13M=function(_13N){return E(_13L);};return [1,B(_12E(_13H,_13M))];},_13O=new T(function(){return B(unCStr("BEL"));}),_13P=7,_13Q=function(_13R){var _13S=new T(function(){return B(A(_13R,[_13P]));}),_13T=function(_13U){return E(_13S);};return [1,B(_12E(_13O,_13T))];},_13V=new T(function(){return B(unCStr("BS"));}),_13W=8,_13X=function(_13Y){var _13Z=new T(function(){return B(A(_13Y,[_13W]));}),_140=function(_141){return E(_13Z);};return [1,B(_12E(_13V,_140))];},_142=new T(function(){return B(unCStr("HT"));}),_143=9,_144=function(_145){var _146=new T(function(){return B(A(_145,[_143]));}),_147=function(_148){return E(_146);};return [1,B(_12E(_142,_147))];},_149=new T(function(){return B(unCStr("LF"));}),_14a=10,_14b=function(_14c){var _14d=new T(function(){return B(A(_14c,[_14a]));}),_14e=function(_14f){return E(_14d);};return [1,B(_12E(_149,_14e))];},_14g=new T(function(){return B(unCStr("VT"));}),_14h=11,_14i=function(_14j){var _14k=new T(function(){return B(A(_14j,[_14h]));}),_14l=function(_14m){return E(_14k);};return [1,B(_12E(_14g,_14l))];},_14n=new T(function(){return B(unCStr("FF"));}),_14o=12,_14p=function(_14q){var _14r=new T(function(){return B(A(_14q,[_14o]));}),_14s=function(_14t){return E(_14r);};return [1,B(_12E(_14n,_14s))];},_14u=new T(function(){return B(unCStr("CR"));}),_14v=13,_14w=function(_14x){var _14y=new T(function(){return B(A(_14x,[_14v]));}),_14z=function(_14A){return E(_14y);};return [1,B(_12E(_14u,_14z))];},_14B=new T(function(){return B(unCStr("SI"));}),_14C=15,_14D=function(_14E){var _14F=new T(function(){return B(A(_14E,[_14C]));}),_14G=function(_14H){return E(_14F);};return [1,B(_12E(_14B,_14G))];},_14I=new T(function(){return B(unCStr("DLE"));}),_14J=16,_14K=function(_14L){var _14M=new T(function(){return B(A(_14L,[_14J]));}),_14N=function(_14O){return E(_14M);};return [1,B(_12E(_14I,_14N))];},_14P=new T(function(){return B(unCStr("DC1"));}),_14Q=17,_14R=function(_14S){var _14T=new T(function(){return B(A(_14S,[_14Q]));}),_14U=function(_14V){return E(_14T);};return [1,B(_12E(_14P,_14U))];},_14W=new T(function(){return B(unCStr("DC2"));}),_14X=18,_14Y=function(_14Z){var _150=new T(function(){return B(A(_14Z,[_14X]));}),_151=function(_152){return E(_150);};return [1,B(_12E(_14W,_151))];},_153=new T(function(){return B(unCStr("DC3"));}),_154=19,_155=function(_156){var _157=new T(function(){return B(A(_156,[_154]));}),_158=function(_159){return E(_157);};return [1,B(_12E(_153,_158))];},_15a=new T(function(){return B(unCStr("DC4"));}),_15b=20,_15c=function(_15d){var _15e=new T(function(){return B(A(_15d,[_15b]));}),_15f=function(_15g){return E(_15e);};return [1,B(_12E(_15a,_15f))];},_15h=new T(function(){return B(unCStr("NAK"));}),_15i=21,_15j=function(_15k){var _15l=new T(function(){return B(A(_15k,[_15i]));}),_15m=function(_15n){return E(_15l);};return [1,B(_12E(_15h,_15m))];},_15o=new T(function(){return B(unCStr("SYN"));}),_15p=22,_15q=function(_15r){var _15s=new T(function(){return B(A(_15r,[_15p]));}),_15t=function(_15u){return E(_15s);};return [1,B(_12E(_15o,_15t))];},_15v=new T(function(){return B(unCStr("ETB"));}),_15w=23,_15x=function(_15y){var _15z=new T(function(){return B(A(_15y,[_15w]));}),_15A=function(_15B){return E(_15z);};return [1,B(_12E(_15v,_15A))];},_15C=new T(function(){return B(unCStr("CAN"));}),_15D=24,_15E=function(_15F){var _15G=new T(function(){return B(A(_15F,[_15D]));}),_15H=function(_15I){return E(_15G);};return [1,B(_12E(_15C,_15H))];},_15J=new T(function(){return B(unCStr("EM"));}),_15K=25,_15L=function(_15M){var _15N=new T(function(){return B(A(_15M,[_15K]));}),_15O=function(_15P){return E(_15N);};return [1,B(_12E(_15J,_15O))];},_15Q=new T(function(){return B(unCStr("SUB"));}),_15R=26,_15S=function(_15T){var _15U=new T(function(){return B(A(_15T,[_15R]));}),_15V=function(_15W){return E(_15U);};return [1,B(_12E(_15Q,_15V))];},_15X=new T(function(){return B(unCStr("ESC"));}),_15Y=27,_15Z=function(_160){var _161=new T(function(){return B(A(_160,[_15Y]));}),_162=function(_163){return E(_161);};return [1,B(_12E(_15X,_162))];},_164=new T(function(){return B(unCStr("FS"));}),_165=28,_166=function(_167){var _168=new T(function(){return B(A(_167,[_165]));}),_169=function(_16a){return E(_168);};return [1,B(_12E(_164,_169))];},_16b=new T(function(){return B(unCStr("GS"));}),_16c=29,_16d=function(_16e){var _16f=new T(function(){return B(A(_16e,[_16c]));}),_16g=function(_16h){return E(_16f);};return [1,B(_12E(_16b,_16g))];},_16i=new T(function(){return B(unCStr("RS"));}),_16j=30,_16k=function(_16l){var _16m=new T(function(){return B(A(_16l,[_16j]));}),_16n=function(_16o){return E(_16m);};return [1,B(_12E(_16i,_16n))];},_16p=new T(function(){return B(unCStr("US"));}),_16q=31,_16r=function(_16s){var _16t=new T(function(){return B(A(_16s,[_16q]));}),_16u=function(_16v){return E(_16t);};return [1,B(_12E(_16p,_16u))];},_16w=new T(function(){return B(unCStr("SP"));}),_16x=32,_16y=function(_16z){var _16A=new T(function(){return B(A(_16z,[_16x]));}),_16B=function(_16C){return E(_16A);};return [1,B(_12E(_16w,_16B))];},_16D=new T(function(){return B(unCStr("DEL"));}),_16E=127,_16F=function(_16G){var _16H=new T(function(){return B(A(_16G,[_16E]));}),_16I=function(_16J){return E(_16H);};return [1,B(_12E(_16D,_16I))];},_16K=[1,_16F,_11],_16L=[1,_16y,_16K],_16M=[1,_16r,_16L],_16N=[1,_16k,_16M],_16O=[1,_16d,_16N],_16P=[1,_166,_16O],_16Q=[1,_15Z,_16P],_16R=[1,_15S,_16Q],_16S=[1,_15L,_16R],_16T=[1,_15E,_16S],_16U=[1,_15x,_16T],_16V=[1,_15q,_16U],_16W=[1,_15j,_16V],_16X=[1,_15c,_16W],_16Y=[1,_155,_16X],_16Z=[1,_14Y,_16Y],_170=[1,_14R,_16Z],_171=[1,_14K,_170],_172=[1,_14D,_171],_173=[1,_14w,_172],_174=[1,_14p,_173],_175=[1,_14i,_174],_176=[1,_14b,_175],_177=[1,_144,_176],_178=[1,_13X,_177],_179=[1,_13Q,_178],_17a=[1,_13J,_179],_17b=[1,_13C,_17a],_17c=[1,_13v,_17b],_17d=[1,_13o,_17c],_17e=[1,_13h,_17d],_17f=[1,_13a,_17e],_17g=[1,_136,_17f],_17h=new T(function(){return B(_12v(_17g));}),_17i=34,_17j=[0,1114111],_17k=92,_17l=39,_17m=function(_17n){var _17o=new T(function(){return B(A(_17n,[_13P]));}),_17p=new T(function(){return B(A(_17n,[_13W]));}),_17q=new T(function(){return B(A(_17n,[_143]));}),_17r=new T(function(){return B(A(_17n,[_14a]));}),_17s=new T(function(){return B(A(_17n,[_14h]));}),_17t=new T(function(){return B(A(_17n,[_14o]));}),_17u=new T(function(){return B(A(_17n,[_14v]));}),_17v=new T(function(){return B(A(_17n,[_17k]));}),_17w=new T(function(){return B(A(_17n,[_17l]));}),_17x=new T(function(){return B(A(_17n,[_17i]));}),_17y=new T(function(){var _17z=function(_17A){var _17B=new T(function(){return B(_10y(E(_17A)));}),_17C=function(_17D){var _17E=B(_11a(_17B,_17D));if(!B(_12l(_17E,_17j))){return [2];}else{var _17F=new T(function(){var _17G=B(_12i(_17E));if(_17G>>>0>1114111){return B(_12f(_17G));}else{return _17G;}});return new F(function(){return A(_17n,[_17F]);});}};return [1,B(_Z6(_17A,_17C))];},_17H=new T(function(){var _17I=new T(function(){return B(A(_17n,[_16q]));}),_17J=new T(function(){return B(A(_17n,[_16j]));}),_17K=new T(function(){return B(A(_17n,[_16c]));}),_17L=new T(function(){return B(A(_17n,[_165]));}),_17M=new T(function(){return B(A(_17n,[_15Y]));}),_17N=new T(function(){return B(A(_17n,[_15R]));}),_17O=new T(function(){return B(A(_17n,[_15K]));}),_17P=new T(function(){return B(A(_17n,[_15D]));}),_17Q=new T(function(){return B(A(_17n,[_15w]));}),_17R=new T(function(){return B(A(_17n,[_15p]));}),_17S=new T(function(){return B(A(_17n,[_15i]));}),_17T=new T(function(){return B(A(_17n,[_15b]));}),_17U=new T(function(){return B(A(_17n,[_154]));}),_17V=new T(function(){return B(A(_17n,[_14X]));}),_17W=new T(function(){return B(A(_17n,[_14Q]));}),_17X=new T(function(){return B(A(_17n,[_14J]));}),_17Y=new T(function(){return B(A(_17n,[_14C]));}),_17Z=new T(function(){return B(A(_17n,[_12T]));}),_180=new T(function(){return B(A(_17n,[_13I]));}),_181=new T(function(){return B(A(_17n,[_13B]));}),_182=new T(function(){return B(A(_17n,[_13u]));}),_183=new T(function(){return B(A(_17n,[_13n]));}),_184=new T(function(){return B(A(_17n,[_13g]));}),_185=new T(function(){return B(A(_17n,[_130]));}),_186=new T(function(){return B(A(_17n,[_139]));}),_187=function(_188){switch(E(_188)){case 64:return E(_186);case 65:return E(_185);case 66:return E(_184);case 67:return E(_183);case 68:return E(_182);case 69:return E(_181);case 70:return E(_180);case 71:return E(_17o);case 72:return E(_17p);case 73:return E(_17q);case 74:return E(_17r);case 75:return E(_17s);case 76:return E(_17t);case 77:return E(_17u);case 78:return E(_17Z);case 79:return E(_17Y);case 80:return E(_17X);case 81:return E(_17W);case 82:return E(_17V);case 83:return E(_17U);case 84:return E(_17T);case 85:return E(_17S);case 86:return E(_17R);case 87:return E(_17Q);case 88:return E(_17P);case 89:return E(_17O);case 90:return E(_17N);case 91:return E(_17M);case 92:return E(_17L);case 93:return E(_17K);case 94:return E(_17J);case 95:return E(_17I);default:return [2];}},_189=[0,_187],_18a=new T(function(){return B(A(_17h,[_17n]));}),_18b=function(_18c){return (E(_18c)==94)?E(_189):[2];};return B(_X9([0,_18b],_18a));});return B(_X9([1,B(_Ym(_12b,_12d,_17z))],_17H));}),_18d=function(_18e){switch(E(_18e)){case 34:return E(_17x);case 39:return E(_17w);case 92:return E(_17v);case 97:return E(_17o);case 98:return E(_17p);case 102:return E(_17t);case 110:return E(_17r);case 114:return E(_17u);case 116:return E(_17q);case 118:return E(_17s);default:return [2];}};return new F(function(){return _X9([0,_18d],_17y);});},_18f=function(_18g){return new F(function(){return A(_18g,[_47]);});},_18h=function(_18i){var _18j=E(_18i);if(!_18j[0]){return E(_18f);}else{var _18k=_18j[2],_18l=E(_18j[1]),_18m=_18l>>>0,_18n=new T(function(){return B(_18h(_18k));});if(_18m>887){var _18o=u_iswspace(_18l);if(!E(_18o)){return E(_18f);}else{var _18p=function(_18q){var _18r=new T(function(){return B(A(_18n,[_18q]));});return [0,function(_18s){return E(_18r);}];};return E(_18p);}}else{var _18t=E(_18m);if(_18t==32){var _18u=function(_18v){var _18w=new T(function(){return B(A(_18n,[_18v]));});return [0,function(_18x){return E(_18w);}];};return E(_18u);}else{if(_18t-9>>>0>4){if(E(_18t)==160){var _18y=function(_18z){var _18A=new T(function(){return B(A(_18n,[_18z]));});return [0,function(_18B){return E(_18A);}];};return E(_18y);}else{return E(_18f);}}else{var _18C=function(_18D){var _18E=new T(function(){return B(A(_18n,[_18D]));});return [0,function(_18F){return E(_18E);}];};return E(_18C);}}}}},_18G=function(_18H){var _18I=new T(function(){return B(_18G(_18H));}),_18J=function(_18K){return (E(_18K)==92)?E(_18I):[2];},_18L=[0,_18J],_18M=function(_18N){return E(_18L);},_18O=function(_18P){return new F(function(){return A(_18h,[_18P,_18M]);});},_18Q=[1,_18O],_18R=new T(function(){var _18S=function(_18T){return new F(function(){return A(_18H,[[0,_18T,_UI]]);});};return B(_17m(_18S));}),_18U=function(_18V){var _18W=E(_18V);if(_18W==38){return E(_18I);}else{var _18X=_18W>>>0;if(_18X>887){var _18Y=u_iswspace(_18W);return (E(_18Y)==0)?[2]:E(_18Q);}else{var _18Z=E(_18X);return (_18Z==32)?E(_18Q):(_18Z-9>>>0>4)?(E(_18Z)==160)?E(_18Q):[2]:E(_18Q);}}},_190=[0,_18U],_191=function(_192){var _193=E(_192);if(E(_193)==92){return E(_18R);}else{return new F(function(){return A(_18H,[[0,_193,_125]]);});}},_194=function(_195){return (E(_195)==92)?E(_190):[2];};return new F(function(){return _X9([0,_194],[0,_191]);});},_196=function(_197,_198){var _199=new T(function(){var _19a=new T(function(){return B(A(_197,[_11]));});return B(A(_198,[[1,_19a]]));}),_19b=function(_19c){var _19d=E(_19c),_19e=E(_19d[1]);if(E(_19e)==34){if(!E(_19d[2])){return E(_199);}else{var _19f=function(_19g){return new F(function(){return A(_197,[[1,_19e,_19g]]);});};return new F(function(){return _196(_19f,_198);});}}else{var _19h=function(_19i){return new F(function(){return A(_197,[[1,_19e,_19i]]);});};return new F(function(){return _196(_19h,_198);});}};return new F(function(){return _18G(_19b);});},_19j=new T(function(){return B(unCStr("_\'"));}),_19k=function(_19l){var _19m=u_iswalnum(_19l);if(!E(_19m)){return new F(function(){return _11X(_Vs,_19l,_19j);});}else{return true;}},_19n=function(_19o){return new F(function(){return _19k(E(_19o));});},_19p=new T(function(){return B(unCStr(",;()[]{}`"));}),_19q=new T(function(){return B(unCStr("=>"));}),_19r=[1,_19q,_11],_19s=new T(function(){return B(unCStr("~"));}),_19t=[1,_19s,_19r],_19u=new T(function(){return B(unCStr("@"));}),_19v=[1,_19u,_19t],_19w=new T(function(){return B(unCStr("->"));}),_19x=[1,_19w,_19v],_19y=new T(function(){return B(unCStr("<-"));}),_19z=[1,_19y,_19x],_19A=new T(function(){return B(unCStr("|"));}),_19B=[1,_19A,_19z],_19C=new T(function(){return B(unCStr("\\"));}),_19D=[1,_19C,_19B],_19E=new T(function(){return B(unCStr("="));}),_19F=[1,_19E,_19D],_19G=new T(function(){return B(unCStr("::"));}),_19H=[1,_19G,_19F],_19I=new T(function(){return B(unCStr(".."));}),_19J=[1,_19I,_19H],_19K=function(_19L){var _19M=new T(function(){return B(A(_19L,[_Z3]));}),_19N=new T(function(){var _19O=new T(function(){var _19P=function(_19Q){var _19R=new T(function(){return B(A(_19L,[[0,_19Q]]));});return [0,function(_19S){return (E(_19S)==39)?E(_19R):[2];}];};return B(_17m(_19P));}),_19T=function(_19U){var _19V=E(_19U);switch(E(_19V)){case 39:return [2];case 92:return E(_19O);default:var _19W=new T(function(){return B(A(_19L,[[0,_19V]]));});return [0,function(_19X){return (E(_19X)==39)?E(_19W):[2];}];}},_19Y=[0,_19T],_19Z=new T(function(){var _1a0=new T(function(){return B(_196(_4b,_19L));}),_1a1=new T(function(){var _1a2=new T(function(){var _1a3=new T(function(){var _1a4=new T(function(){return [1,B(_Ym(_11V,_11H,_19L))];}),_1a5=function(_1a6){var _1a7=E(_1a6),_1a8=u_iswalpha(_1a7);if(!E(_1a8)){if(E(_1a7)==95){var _1a9=function(_1aa){return new F(function(){return A(_19L,[[3,[1,_1a7,_1aa]]]);});};return [1,B(_YN(_19n,_1a9))];}else{return [2];}}else{var _1ab=function(_1ac){return new F(function(){return A(_19L,[[3,[1,_1a7,_1ac]]]);});};return [1,B(_YN(_19n,_1ab))];}};return B(_X9([0,_1a5],_1a4));}),_1ad=function(_1ae){if(!B(_11X(_Vs,_1ae,_122))){return [2];}else{var _1af=function(_1ag){var _1ah=[1,_1ae,_1ag];if(!B(_11X(_Uk,_1ah,_19J))){return new F(function(){return A(_19L,[[4,_1ah]]);});}else{return new F(function(){return A(_19L,[[2,_1ah]]);});}};return [1,B(_YN(_123,_1af))];}};return B(_X9([0,_1ad],_1a3));}),_1ai=function(_1aj){if(!B(_11X(_Vs,_1aj,_19p))){return [2];}else{return new F(function(){return A(_19L,[[2,[1,_1aj,_11]]]);});}};return B(_X9([0,_1ai],_1a2));}),_1ak=function(_1al){return (E(_1al)==34)?E(_1a0):[2];};return B(_X9([0,_1ak],_1a1));}),_1am=function(_1an){return (E(_1an)==39)?E(_19Y):[2];};return B(_X9([0,_1am],_19Z));}),_1ao=function(_1ap){return (E(_1ap)[0]==0)?E(_19M):[2];};return new F(function(){return _X9([1,_1ao],_19N);});},_1aq=0,_1ar=function(_1as,_1at){var _1au=new T(function(){var _1av=new T(function(){var _1aw=function(_1ax){var _1ay=new T(function(){var _1az=new T(function(){return B(A(_1at,[_1ax]));}),_1aA=function(_1aB){var _1aC=E(_1aB);return (_1aC[0]==2)?(!B(_NC(_1aC[1],_XV)))?[2]:E(_1az):[2];};return B(_19K(_1aA));}),_1aD=function(_1aE){return E(_1ay);};return [1,function(_1aF){return new F(function(){return A(_18h,[_1aF,_1aD]);});}];};return B(A(_1as,[_1aq,_1aw]));}),_1aG=function(_1aH){var _1aI=E(_1aH);return (_1aI[0]==2)?(!B(_NC(_1aI[1],_XU)))?[2]:E(_1av):[2];};return B(_19K(_1aG));}),_1aJ=function(_1aK){return E(_1au);};return function(_1aL){return new F(function(){return A(_18h,[_1aL,_1aJ]);});};},_1aM=function(_1aN,_1aO){var _1aP=function(_1aQ){var _1aR=new T(function(){return B(A(_1aN,[_1aQ]));}),_1aS=function(_1aT){var _1aU=new T(function(){return [1,B(_1ar(_1aP,_1aT))];});return new F(function(){return _X9(B(A(_1aR,[_1aT])),_1aU);});};return E(_1aS);},_1aV=new T(function(){return B(A(_1aN,[_1aO]));}),_1aW=function(_1aX){var _1aY=new T(function(){return [1,B(_1ar(_1aP,_1aX))];});return new F(function(){return _X9(B(A(_1aV,[_1aX])),_1aY);});};return E(_1aW);},_1aZ=function(_1b0,_1b1){var _1b2=function(_1b3,_1b4){var _1b5=function(_1b6){var _1b7=new T(function(){return  -E(_1b6);});return new F(function(){return A(_1b4,[_1b7]);});},_1b8=function(_1b9){return new F(function(){return A(_1b0,[_1b9,_1b3,_1b5]);});},_1ba=new T(function(){return B(_19K(_1b8));}),_1bb=function(_1bc){return E(_1ba);},_1bd=function(_1be){return new F(function(){return A(_18h,[_1be,_1bb]);});},_1bf=[1,_1bd],_1bg=function(_1bh){var _1bi=E(_1bh);if(_1bi[0]==4){var _1bj=E(_1bi[1]);if(!_1bj[0]){return new F(function(){return A(_1b0,[_1bi,_1b3,_1b4]);});}else{if(E(_1bj[1])==45){if(!E(_1bj[2])[0]){return E(_1bf);}else{return new F(function(){return A(_1b0,[_1bi,_1b3,_1b4]);});}}else{return new F(function(){return A(_1b0,[_1bi,_1b3,_1b4]);});}}}else{return new F(function(){return A(_1b0,[_1bi,_1b3,_1b4]);});}},_1bk=new T(function(){return B(_19K(_1bg));}),_1bl=function(_1bm){return E(_1bk);};return [1,function(_1bn){return new F(function(){return A(_18h,[_1bn,_1bl]);});}];};return new F(function(){return _1aM(_1b2,_1b1);});},_1bo=function(_1bp){var _1bq=E(_1bp);if(!_1bq[0]){var _1br=_1bq[1],_1bs=_1bq[2];return [1,new T(function(){var _1bt=new T(function(){return B(_NK(_1bs,0));},1),_1bu=new T(function(){return B(_10y(E(_1br)));});return B(_10U(_1bu,_1bt,B(_wI(_10A,_1bs))));})];}else{var _1bv=_1bq[1];if(!E(_1bq[2])[0]){if(!E(_1bq[3])[0]){return [1,new T(function(){return B(_11a(_10x,_1bv));})];}else{return [0];}}else{return [0];}}},_1bw=function(_1bx,_1by){return [2];},_1bz=function(_1bA){var _1bB=E(_1bA);if(_1bB[0]==5){var _1bC=B(_1bo(_1bB[1]));if(!_1bC[0]){return E(_1bw);}else{var _1bD=_1bC[1],_1bE=new T(function(){return B(_12i(_1bD));}),_1bF=function(_1bG,_1bH){return new F(function(){return A(_1bH,[_1bE]);});};return E(_1bF);}}else{return E(_1bw);}},_1bI=function(_1bJ){var _1bK=[3,_1bJ,_Yd],_1bL=function(_1bM){return E(_1bK);};return [1,function(_1bN){return new F(function(){return A(_18h,[_1bN,_1bL]);});}];},_1bO=new T(function(){return B(A(_1aZ,[_1bz,_1aq,_1bI]));}),_1bP=function(_1bQ){while(1){var _1bR=(function(_1bS){var _1bT=E(_1bS);if(!_1bT[0]){return [0];}else{var _1bU=_1bT[2],_1bV=E(_1bT[1]);if(!E(_1bV[2])[0]){var _1bW=new T(function(){return B(_1bP(_1bU));});return [1,_1bV[1],_1bW];}else{_1bQ=_1bU;return null;}}})(_1bQ);if(_1bR!=null){return _1bR;}}},_1bX=function() { $('.selectpicker').selectpicker(); },_1bY=new T(function(){return B(unCStr("head"));}),_1bZ=new T(function(){return B(_a7(_1bY));}),_1c0=function(_1c1,_1c2){while(1){var _1c3=E(_1c2);if(!_1c3[0]){_1c1=_1c3[3];_1c2=_1c3[4];continue;}else{return E(_1c1);}}},_1c4=function(_1c5,_1c6){while(1){var _1c7=(function(_1c8,_1c9){var _1ca=E(_1c9);if(!_1ca[0]){var _1cb=_1ca[5],_1cc=new T(function(){return B(_1c4(_1c8,_1cb));});_1c5=[1,_1ca[2],_1cc];_1c6=_1ca[4];return null;}else{return E(_1c8);}})(_1c5,_1c6);if(_1c7!=null){return _1c7;}}},_1cd=new T(function(){return B(unCStr("</tr>"));}),_1ce=new T(function(){return B(unCStr("\">\u7de8\u96c6</button></td>"));}),_1cf=new T(function(){return B(_v(_1ce,_1cd));}),_1cg=new T(function(){return B(unCStr("\u30fb"));}),_1ch=new T(function(){return B(unCStr("<tr>"));}),_1ci=function(_1cj,_1ck){while(1){var _1cl=(function(_1cm,_1cn){var _1co=E(_1cn);switch(_1co[0]){case 0:var _1cp=_1co[4],_1cq=new T(function(){return B(_1ci(_1cm,_1cp));},1);_1cj=_1cq;_1ck=_1co[3];return null;case 1:var _1cr=_1co[1],_1cs=_1co[2],_1ct=new T(function(){var _1cu=new T(function(){var _1cv=new T(function(){var _1cw=new T(function(){var _1cx=new T(function(){var _1cy=new T(function(){var _1cz=new T(function(){var _1cA=new T(function(){return B(_v(B(_H(0,_1cr,_11)),_1cf));});return B(unAppCStr("</td>  <td><button type=\"button\" class=\"btn btn-default btn-sm\" id=\"edit-tactic-",_1cA));},1);return B(_v(B(_H(0,E(B(_1c0(_1bZ,_1cs))[2]),_11)),_1cz));});return B(unAppCStr("</td>  <td>",_1cy));}),_1cB=B(_1c4(_11,_1cs));if(!_1cB[0]){return E(_1cx);}else{var _1cC=_1cB[2],_1cD=function(_1cE){var _1cF=E(_1cE);if(!_1cF[0]){return E(_1cx);}else{var _1cG=_1cF[2],_1cH=new T(function(){return B(_1cD(_1cG));},1);return new F(function(){return _v(_1cF[1],_1cH);});}},_1cI=function(_1cJ,_1cK){var _1cL=new T(function(){return B(_1cD(_1cK));},1);return new F(function(){return _v(_1cJ,_1cL);});},_1cM=new T(function(){return B(_wQ(_1cg,_1cC));});return B(_1cI(_1cB[1],_1cM));}});return B(unAppCStr("</td>  <td>",_1cw));},1);return B(_v(B(_H(0,_1cr,_11)),_1cv));});return B(unAppCStr("  <td>",_1cu));},1);return new F(function(){return _v(B(_v(_1ch,_1ct)),_1cm);});break;default:return E(_1cm);}})(_1cj,_1ck);if(_1cl!=null){return _1cl;}}},_1cN=function(_1cO){var _1cP=E(_1cO);if(!_1cP[0]){var _1cQ=_1cP[3],_1cR=_1cP[4];if(_1cP[2]>=0){var _1cS=new T(function(){return B(_1ci(_11,_1cR));},1);return new F(function(){return _1ci(_1cS,_1cQ);});}else{var _1cT=new T(function(){return B(_1ci(_11,_1cQ));},1);return new F(function(){return _1ci(_1cT,_1cR);});}}else{return new F(function(){return _1ci(_11,_1cP);});}},_1cU=function(_1cV){while(1){var _1cW=E(_1cV);if(!_1cW[0]){_1cV=[1,I_fromInt(_1cW[1])];continue;}else{return new F(function(){return I_toString(_1cW[1]);});}}},_1cX=function(_1cY,_1cZ){return new F(function(){return _v(fromJSStr(B(_1cU(_1cY))),_1cZ);});},_1d0=function(_1d1,_1d2){var _1d3=E(_1d1);if(!_1d3[0]){var _1d4=_1d3[1],_1d5=E(_1d2);return (_1d5[0]==0)?_1d4<_1d5[1]:I_compareInt(_1d5[1],_1d4)>0;}else{var _1d6=_1d3[1],_1d7=E(_1d2);return (_1d7[0]==0)?I_compareInt(_1d6,_1d7[1])<0:I_compare(_1d6,_1d7[1])<0;}},_1d8=[0,0],_1d9=function(_1da,_1db,_1dc){if(_1da<=6){return new F(function(){return _1cX(_1db,_1dc);});}else{if(!B(_1d0(_1db,_1d8))){return new F(function(){return _1cX(_1db,_1dc);});}else{var _1dd=new T(function(){return B(_v(fromJSStr(B(_1cU(_1db))),[1,_F,_1dc]));});return [1,_G,_1dd];}}},_1de=new T(function(){return B(unCStr("</th>"));}),_1df=function(_1dg,_1dh){while(1){var _1di=(function(_1dj,_1dk){var _1dl=E(_1dk);if(!_1dl[0]){var _1dm=_1dl[2],_1dn=_1dl[5],_1do=new T(function(){var _1dp=new T(function(){return B(_1df(_1dj,_1dn));},1),_1dq=new T(function(){return B(_v(_1dm,_1de));});return B(_v(B(unAppCStr("<th>",_1dq)),_1dp));},1);_1dg=_1do;_1dh=_1dl[4];return null;}else{return E(_1dj);}})(_1dg,_1dh);if(_1di!=null){return _1di;}}},_1dr=function(_1ds){var _1dt=E(_1ds);if(!_1dt[0]){return E(_1cd);}else{var _1du=_1dt[2],_1dv=new T(function(){return B(_1dr(_1du));},1);return new F(function(){return _v(_1dt[1],_1dv);});}},_1dw=function(_1dx,_1dy){while(1){var _1dz=(function(_1dA,_1dB){var _1dC=E(_1dB);switch(_1dC[0]){case 0:var _1dD=_1dC[4],_1dE=new T(function(){return B(_1dw(_1dA,_1dD));});_1dx=_1dE;_1dy=_1dC[3];return null;case 1:var _1dF=_1dC[2],_1dG=new T(function(){return B(_9I(_1dF));});return [1,_1dG,_1dA];default:return E(_1dA);}})(_1dx,_1dy);if(_1dz!=null){return _1dz;}}},_1dH=new T(function(){return B(_wo(0,2147483647));}),_1dI=function(_1dJ,_1dK){while(1){var _1dL=(function(_1dM,_1dN){var _1dO=E(_1dN);if(!_1dO[0]){var _1dP=_1dO[3],_1dQ=_1dO[5],_1dR=new T(function(){return B(_1dI(_1dM,_1dQ));}),_1dS=new T(function(){var _1dT=new T(function(){var _1dU=E(E(_1dP)[3]);if(!_1dU[0]){var _1dV=_1dU[3],_1dW=_1dU[4];if(_1dU[2]>=0){var _1dX=new T(function(){return B(_1dw(_11,_1dW));});return B(_1dw(_1dX,_1dV));}else{var _1dY=new T(function(){return B(_1dw(_11,_1dV));});return B(_1dw(_1dY,_1dW));}}else{return B(_1dw(_11,_1dU));}},1);return B(_NT(_1dH,_1dT));});_1dJ=[1,_1dS,_1dR];_1dK=_1dO[4];return null;}else{return E(_1dM);}})(_1dJ,_1dK);if(_1dL!=null){return _1dL;}}},_1dZ=new T(function(){return B(unCStr("</option>"));}),_1e0=0,_1e1=1,_1e2=[1,_1e1,_11],_1e3=[1,_1e0,_1e2],_1e4=new T(function(){return B(_wI(_9I,_1e3));}),_1e5=new T(function(){return B(unCStr("</td>"));}),_1e6=new T(function(){return B(unCStr("</select>"));}),_1e7=new T(function(){return B(_v(_1e6,_1e5));}),_1e8=function(_1e9,_1ea){var _1eb=E(_1e9);if(!_1eb[0]){return [0];}else{var _1ec=_1eb[1],_1ed=_1eb[2],_1ee=E(_1ea);if(!_1ee[0]){return [0];}else{var _1ef=_1ee[1],_1eg=_1ee[2],_1eh=new T(function(){return B(_1e8(_1ed,_1eg));}),_1ei=new T(function(){var _1ej=new T(function(){var _1ek=E(_1ef),_1el=_1ek[1],_1em=_1ek[2],_1en=new T(function(){var _1eo=new T(function(){var _1ep=new T(function(){var _1eq=new T(function(){var _1er=new T(function(){var _1es=function(_1et){var _1eu=E(_1et);if(!_1eu[0]){return E(_1e7);}else{var _1ev=_1eu[1],_1ew=_1eu[2];if(!B(_NC(_1em,_1ev))){var _1ex=new T(function(){return B(_1es(_1ew));},1),_1ey=new T(function(){return B(_v(_1ev,_1dZ));});return new F(function(){return _v(B(unAppCStr("<option>",_1ey)),_1ex);});}else{var _1ez=new T(function(){return B(_1es(_1ew));},1),_1eA=new T(function(){return B(_v(_1ev,_1dZ));});return new F(function(){return _v(B(unAppCStr("<option selected>",_1eA)),_1ez);});}}};return B(_1es(_1e4));});return B(unAppCStr("\">",_1er));},1);return B(_v(B(_H(0,E(_1el),_11)),_1eq));});return B(unAppCStr("-",_1ep));},1);return B(_v(_1ec,_1eo));});return B(unAppCStr("<select class=\"selectpicker\" id=\"select-",_1en));});return B(unAppCStr("<td>",_1ej));});return [1,_1ei,_1eh];}}},_1eB=new T(function(){return B(_v(_og,_11));}),_1eC=function(_1eD){var _1eE=E(_1eD);if(!_1eE[0]){return [0];}else{var _1eF=_1eE[2],_1eG=new T(function(){return B(_1eC(_1eF));},1);return new F(function(){return _v(_1eE[1],_1eG);});}},_1eH=function(_1eI,_1eJ){var _1eK=new T(function(){return B(_1eC(_1eJ));},1);return new F(function(){return _v(_1eI,_1eK);});},_1eL=[1,_oi,_11],_1eM=new T(function(){return B(unCStr("    <button class=\"btn btn-default\" id=\"edit-tactic-done\">\u5b8c\u4e86</button>"));}),_1eN=[1,_1eM,_1eL],_1eO=new T(function(){return B(unCStr("  <div class=\"panel-footer\">"));}),_1eP=new T(function(){return B(_1eH(_1eO,_1eN));}),_1eQ=new T(function(){return B(unCStr("      </tbody>"));}),_1eR=new T(function(){return B(unCStr("    </table>"));}),_1eS=[1,_1eR,_1eL],_1eT=new T(function(){return B(unCStr("        </tr>"));}),_1eU=new T(function(){return B(unCStr("      </thead>"));}),_1eV=new T(function(){return B(unCStr("      <tbody>"));}),_1eW=[1,_1eV,_11],_1eX=[1,_1eU,_1eW],_1eY=function(_1eZ,_1f0){var _1f1=E(_1eZ),_1f2=new T(function(){var _1f3=B(_1eY(B(_10j(_1f1,_1f0)),_1f0));return [1,_1f3[1],_1f3[2]];});return [0,_1f1,_1f2];},_1f4=[0,1],_1f5=new T(function(){var _1f6=B(_1eY(_1f4,_1f4));return [1,_1f6[1],_1f6[2]];}),_1f7=new T(function(){return B(unCStr("          <th>T</th>"));}),_1f8=[1,_1f7,_11],_1f9=new T(function(){return B(unCStr("        <tr>"));}),_1fa=[1,_1f9,_1f8],_1fb=new T(function(){return B(unCStr("      <thead>"));}),_1fc=[1,_1fb,_1fa],_1fd=new T(function(){return B(unCStr("    <table class=\"table\">"));}),_1fe=[1,_1fd,_1fc],_1ff=new T(function(){return B(unCStr("  <div class=\"panel-body\">"));}),_1fg=new T(function(){return B(unCStr("<div class=\"panel panel-default\" id=\"tactic-detail-table\">"));}),_1fh=function(_1fi){while(1){var _1fj=(function(_1fk){var _1fl=E(_1fk);if(!_1fl[0]){return [0];}else{var _1fm=_1fl[2],_1fn=E(_1fl[1]);if(!_1fn[0]){_1fi=_1fm;return null;}else{var _1fo=new T(function(){return B(_1fh(_1fm));});return [1,_1fn[2],_1fo];}}})(_1fi);if(_1fj!=null){return _1fj;}}},_1fp=function(_1fq){while(1){var _1fr=(function(_1fs){var _1ft=E(_1fs);if(!_1ft[0]){return [0];}else{var _1fu=_1ft[2],_1fv=E(_1ft[1]);if(!_1fv[0]){_1fq=_1fu;return null;}else{var _1fw=new T(function(){return B(_1fp(_1fu));});return [1,_1fv[1],_1fw];}}})(_1fq);if(_1fr!=null){return _1fr;}}},_1fx=function(_1fy){while(1){var _1fz=(function(_1fA){var _1fB=E(_1fA);if(!_1fB[0]){return [0];}else{var _1fC=_1fB[2],_1fD=E(_1fB[1]);if(!_1fD[0]){_1fy=_1fC;return null;}else{var _1fE=_1fD[2],_1fF=new T(function(){var _1fG=new T(function(){return B(_1fh(_1fC));});return B(_1fx([1,_1fE,_1fG]));}),_1fH=new T(function(){return B(_1fp(_1fC));});return [1,[1,_1fD[1],_1fH],_1fF];}}})(_1fy);if(_1fz!=null){return _1fz;}}},_1fI=function(_1fJ,_1fK,_1fL){var _1fM=new T(function(){var _1fN=new T(function(){var _1fO=new T(function(){var _1fP=new T(function(){var _1fQ=new T(function(){var _1fR=new T(function(){var _1fS=new T(function(){var _1fT=new T(function(){var _1fU=new T(function(){if(!E(_1fK)){return E(_1eB);}else{return E(_1eP);}}),_1fV=function(_1fW){var _1fX=E(_1fW);if(!_1fX[0]){return E(_1fU);}else{var _1fY=_1fX[2],_1fZ=new T(function(){return B(_1fV(_1fY));},1);return new F(function(){return _v(_1fX[1],_1fZ);});}},_1g0=function(_1g1,_1g2){var _1g3=new T(function(){return B(_1fV(_1g2));},1);return new F(function(){return _v(_1g1,_1g3);});};return B(_1g0(_1eQ,_1eS));}),_1g4=function(_1g5,_1g6){var _1g7=E(_1g5);if(!_1g7[0]){return E(_1fT);}else{var _1g8=_1g7[1],_1g9=_1g7[2],_1ga=E(_1g6);if(!_1ga[0]){return E(_1fT);}else{var _1gb=_1ga[1],_1gc=_1ga[2],_1gd=new T(function(){return B(_1g4(_1g9,_1gc));},1),_1ge=new T(function(){var _1gf=new T(function(){var _1gg=new T(function(){return B(_1dr(_1gb));});return B(unAppCStr("</td>",_1gg));},1);return B(_v(B(_1d9(0,_1g8,_11)),_1gf));});return new F(function(){return _v(B(unAppCStr("<tr><td>",_1ge)),_1gd);});}}},_1gh=new T(function(){var _1gi=new T(function(){return B(_1c4(_11,_1fL));}),_1gj=function(_1gk){return new F(function(){return _1e8(_1gi,_1gk);});};return B(_wI(_1gj,B(_1fx(B(_1dI(_11,_1fL))))));},1);return B(_1g4(_1f5,_1gh));}),_1gl=function(_1gm){var _1gn=E(_1gm);if(!_1gn[0]){return E(_1fS);}else{var _1go=_1gn[2],_1gp=new T(function(){return B(_1gl(_1go));},1);return new F(function(){return _v(_1gn[1],_1gp);});}},_1gq=function(_1gr,_1gs){var _1gt=new T(function(){return B(_1gl(_1gs));},1);return new F(function(){return _v(_1gr,_1gt);});};return B(_1gq(_1eT,_1eX));},1);return B(_1df(_1fR,_1fL));}),_1gu=function(_1gv){var _1gw=E(_1gv);if(!_1gw[0]){return E(_1fQ);}else{var _1gx=_1gw[2],_1gy=new T(function(){return B(_1gu(_1gx));},1);return new F(function(){return _v(_1gw[1],_1gy);});}},_1gz=function(_1gA,_1gB){var _1gC=new T(function(){return B(_1gu(_1gB));},1);return new F(function(){return _v(_1gA,_1gC);});};return B(_1gz(_1ff,_1fe));});return B(unAppCStr("</div>",_1fP));},1);return B(_v(_1fJ,_1fO));});return B(unAppCStr("  <div class=\"panel-heading\">",_1fN));},1);return new F(function(){return _v(_1fg,_1fM);});},_1gD=2,_1gE=[1,_1gD,_11],_1gF=function(_1gG){var _1gH=new T(function(){return B(_NC(_9F,_1gG));}),_1gI=new T(function(){return B(_NC(_9G,_1gG));});if(!B(_NC(_9H,_1gG))){var _1gJ=function(_1gK){while(1){var _1gL=E(_1gK);if(!_1gL[0]){return E(_1bZ);}else{var _1gM=_1gL[2];switch(E(_1gL[1])){case 0:_1gK=_1gM;continue;case 1:if(!E(_1gI)){_1gK=_1gM;continue;}else{return 1;}break;default:if(!E(_1gH)){_1gK=_1gM;continue;}else{return 2;}}}}},_1gN=_1gE;if(!E(_1gI)){return new F(function(){return _1gJ(_1gN);});}else{return 1;}}else{return 0;}},_1gO=function(_1gP,_1gQ,_){var _1gR=jsQuerySelectorAll(_1gP,toJSStr(_Vk));if(!_1gR[0]){return E(_n1);}else{var _1gS=_1gR[1];if(!E(_1gR[2])[0]){var _1gT=E(_1gQ),_1gU=rMV(_1gT),_1gV=_1gU,_1gW=new T(function(){return B(_1cN(E(E(_1gV)[7])[4]));}),_1gX=B(A(_l3,[_4d,_4S,_1gS,_l2,_1gW,_])),_1gY=rMV(_1gT),_1gZ=function(_1h0,_1h1,_){while(1){var _1h2=(function(_1h3,_1h4,_){var _1h5=E(_1h4);switch(_1h5[0]){case 0:var _1h6=_1h5[4],_1h7=function(_){return new F(function(){return _1gZ(_1h3,_1h6,_);});};_1h0=_1h7;_1h1=_1h5[3];return null;case 1:var _1h8=_1h5[1],_1h9=new T(function(){var _1ha=new T(function(){return B(_H(0,_1h8,_11));});return B(unAppCStr("edit-tactic-",_1ha));}),_1hb=jsQuerySelectorAll(E(_1gS),toJSStr([1,_lA,_1h9]));if(!_1hb[0]){return E(_n1);}else{if(!E(_1hb[2])[0]){var _1hc=new T(function(){var _1hd=new T(function(){return B(_H(0,_1h8,_11));});return B(unAppCStr("# ",_1hd));}),_1he=function(_1hf,_){var _1hg=jsQuerySelectorAll(_1gP,toJSStr(_Vi));if(!_1hg[0]){return E(_n1);}else{var _1hh=_1hg[1];if(!E(_1hg[2])[0]){var _1hi=rMV(_1gT),_1hj=_1hi,_1hk=new T(function(){var _1hl=new T(function(){return B(_es(E(E(_1hj)[7])[4],_1h8));});return B(_1fI(_1hc,_UI,_1hl));}),_1hm=B(A(_l3,[_4d,_4S,_1hh,_l2,_1hk,_])),_1hn=E(_1bX)(E(_3z)),_1ho=E(_1hh),_1hp=jsQuerySelectorAll(_1ho,toJSStr(_Vg));if(!_1hp[0]){return E(_n1);}else{if(!E(_1hp[2])[0]){var _1hq=function(_1hr,_){var _1hs=jsQuerySelectorAll(_1gP,toJSStr(_Ve));if(!_1hs[0]){return E(_n1);}else{if(!E(_1hs[2])[0]){var _1ht=jsQuerySelectorAll(E(_1hs[1]),toJSStr(E(_WR)));if(!_1ht[0]){return new F(function(){return A(_l3,[_4d,_4S,_1ho,_l2,_11,_]);});}else{var _1hu=E(_1ht[1]),_1hv=E(_Vc),_1hw=jsGet(_1hu,_1hv),_1hx=_1hw,_1hy=B(A(_V0,[_4d,_4S,_1hu,_Vl,_])),_1hz=B(A(_WQ,[_1hy]));if(!_1hz[0]){return new F(function(){return _UH(_);});}else{var _1hA=E(_1hz[2]);if(!_1hA[0]){return new F(function(){return _UH(_);});}else{var _1hB=_1hA[1],_1hC=E(_1hA[2]);if(!_1hC[0]){return new F(function(){return _UH(_);});}else{var _1hD=_1hC[1];if(!E(_1hC[2])[0]){var _1hE=rMV(_1gT),_1hF=E(_1hE),_1hG=_1hF[7],_1hH=new T(function(){var _1hI=E(_1hG),_1hJ=_1hI[4],_1hK=new T(function(){var _1hL=new T(function(){var _1hM=B(_es(_1hJ,_1h8)),_1hN=new T(function(){var _1hO=B(_UM(_UD,_1hB,_1hM)),_1hP=_1hO[3],_1hQ=new T(function(){var _1hR=B(_1bP(B(_WX(_1bO,_1hD))));if(!_1hR[0]){return E(_WT);}else{if(!E(_1hR[2])[0]){var _1hS=new T(function(){return B(_1gF(fromJSStr(_1hx)));});return B(_gB(E(_1hR[1]),_1hS,_1hP));}else{return E(_WV);}}});return [0,_1hO[1],_1hO[2],_1hQ];});return B(_8A(_1hB,_1hN,_1hM));});return B(_gB(_1h8,_1hL,_1hJ));});return [0,_1hI[1],_1hI[2],_1hI[3],_1hK,_1hI[5]];}),_=wMV(_1gT,[0,_1hF[1],_1hF[2],_1hF[3],_1hF[4],_1hF[5],_1hF[6],_1hH]),_1hT=function(_1hU,_){while(1){var _1hV=(function(_1hW,_){var _1hX=E(_1hW);if(!_1hX[0]){return _47;}else{var _1hY=E(_1hX[1]),_1hZ=jsGet(_1hY,_1hv),_1i0=_1hZ,_1i1=B(A(_V0,[_4d,_4S,_1hY,_Vl,_])),_1i2=B(A(_WQ,[_1i1]));if(!_1i2[0]){return new F(function(){return _UH(_);});}else{var _1i3=E(_1i2[2]);if(!_1i3[0]){return new F(function(){return _UH(_);});}else{var _1i4=_1i3[1],_1i5=E(_1i3[2]);if(!_1i5[0]){return new F(function(){return _UH(_);});}else{var _1i6=_1i5[1];if(!E(_1i5[2])[0]){var _1i7=rMV(_1gT),_1i8=E(_1i7),_1i9=_1i8[7],_1ia=new T(function(){var _1ib=E(_1i9),_1ic=_1ib[4],_1id=new T(function(){var _1ie=new T(function(){var _1if=B(_es(_1ic,_1h8)),_1ig=new T(function(){var _1ih=B(_UM(_UD,_1i4,_1if)),_1ii=_1ih[3],_1ij=new T(function(){var _1ik=B(_1bP(B(_WX(_1bO,_1i6))));if(!_1ik[0]){return E(_WT);}else{if(!E(_1ik[2])[0]){var _1il=new T(function(){return B(_1gF(fromJSStr(_1i0)));});return B(_gB(E(_1ik[1]),_1il,_1ii));}else{return E(_WV);}}});return [0,_1ih[1],_1ih[2],_1ij];});return B(_8A(_1i4,_1ig,_1if));});return B(_gB(_1h8,_1ie,_1ic));});return [0,_1ib[1],_1ib[2],_1ib[3],_1id,_1ib[5]];}),_=wMV(_1gT,[0,_1i8[1],_1i8[2],_1i8[3],_1i8[4],_1i8[5],_1i8[6],_1ia]);_1hU=_1hX[2];return null;}else{return new F(function(){return _UH(_);});}}}}}})(_1hU,_);if(_1hV!=null){return _1hV;}}},_1im=B(_1hT(_1ht[2],_));return new F(function(){return A(_l3,[_4d,_4S,_1ho,_l2,_11,_]);});}else{return new F(function(){return _UH(_);});}}}}}}else{return E(_n1);}}},_1in=B(A(_yE,[_4T,_4d,_46,_1hp[1],_w4,_1hq,_]));return _47;}else{return E(_n1);}}}else{return E(_n1);}}},_1io=B(A(_yE,[_4T,_4d,_46,_1hb[1],_w4,_1he,_]));return new F(function(){return A(_1h3,[_]);});}else{return E(_n1);}}break;default:return new F(function(){return A(_1h3,[_]);});}})(_1h0,_1h1,_);if(_1h2!=null){return _1h2;}}},_1ip=E(E(E(_1gY)[7])[4]);if(!_1ip[0]){var _1iq=_1ip[3],_1ir=_1ip[4];if(_1ip[2]>=0){var _1is=function(_){return new F(function(){return _1gZ(_UJ,_1ir,_);});};return new F(function(){return _1gZ(_1is,_1iq,_);});}else{var _1it=function(_){return new F(function(){return _1gZ(_UJ,_1iq,_);});};return new F(function(){return _1gZ(_1it,_1ir,_);});}}else{return new F(function(){return _1gZ(_UJ,_1ip,_);});}}else{return E(_n1);}}},_1iu=0,_1iv=1,_1iw=function(_1ix,_1iy){while(1){var _1iz=E(_1iy);if(!_1iz[0]){return [0];}else{var _1iA=_1iz[2],_1iB=E(_1ix);if(_1iB==1){return E(_1iA);}else{_1ix=_1iB-1|0;_1iy=_1iA;continue;}}}},_1iC=function(_1iD,_1iE,_1iF){var _1iG=E(_1iD);if(_1iG==1){return E(_1iF);}else{return new F(function(){return _1iw(_1iG-1|0,_1iF);});}},_1iH=function(_1iI,_1iJ){var _1iK=E(_1iJ);if(!_1iK[0]){return [0];}else{var _1iL=_1iK[1],_1iM=_1iK[2],_1iN=E(_1iI);if(_1iN==1){return [1,_1iL,_11];}else{var _1iO=new T(function(){return B(_1iH(_1iN-1|0,_1iM));});return [1,_1iL,_1iO];}}},_1iP=function(_1iQ,_1iR,_1iS){var _1iT=new T(function(){if(_1iQ>0){return B(_1iU(_1iQ,B(_1iC(_1iQ,_1iR,_1iS))));}else{return B(_1iP(_1iQ,_1iR,_1iS));}}),_1iV=new T(function(){if(0>=_1iQ){return [0];}else{return B(_1iH(_1iQ,[1,_1iR,_1iS]));}});return [1,_1iV,_1iT];},_1iU=function(_1iW,_1iX){var _1iY=E(_1iX);if(!_1iY[0]){return [0];}else{var _1iZ=_1iY[1],_1j0=_1iY[2],_1j1=new T(function(){if(_1iW>0){return B(_1iU(_1iW,B(_1iC(_1iW,_1iZ,_1j0))));}else{return B(_1iP(_1iW,_1iZ,_1j0));}}),_1j2=new T(function(){if(0>=_1iW){return [0];}else{return B(_1iH(_1iW,_1iY));}});return [1,_1j2,_1j1];}},_1j3=function(_1j4,_1j5,_1j6,_1j7){var _1j8=E(_1j7);if(!_1j8[0]){var _1j9=_1j8[3],_1ja=_1j8[4],_1jb=_1j8[5],_1jc=E(_1j8[2]),_1jd=E(_1j4),_1je=E(_1jc[1]);if(_1jd>=_1je){if(_1jd!=_1je){return new F(function(){return _5G(_1jc,_1j9,_1ja,B(_1j3(_1jd,_1j5,_1j6,_1jb)));});}else{var _1jf=E(_1j5),_1jg=E(_1jc[2]);if(_1jf>=_1jg){if(_1jf!=_1jg){return new F(function(){return _5G(_1jc,_1j9,_1ja,B(_1j3(_1jd,_1jf,_1j6,_1jb)));});}else{return [0,_1j8[1],[0,_1jd,_1jf],_1j6,E(_1ja),E(_1jb)];}}else{return new F(function(){return _6z(_1jc,_1j9,B(_1j3(_1jd,_1jf,_1j6,_1ja)),_1jb);});}}}else{return new F(function(){return _6z(_1jc,_1j9,B(_1j3(_1jd,_1j5,_1j6,_1ja)),_1jb);});}}else{return [0,1,[0,_1j4,_1j5],_1j6,E(_5B),E(_5B)];}},_1jh=function(_1ji){var _1jj=E(_1ji);if(!_1jj[0]){return [0];}else{var _1jk=_1jj[2],_1jl=new T(function(){return B(_1jh(_1jk));},1);return new F(function(){return _v(_1jj[1],_1jl);});}},_1jm=function(_1jn){return new F(function(){return _1jh(_1jn);});},_1jo=(function(s){return s[0];}),_1jp=function(_1jq,_1jr){var _1js=_1jq%_1jr;if(_1jq<=0){if(_1jq>=0){return E(_1js);}else{if(_1jr<=0){return E(_1js);}else{var _1jt=E(_1js);return (_1jt==0)?0:_1jt+_1jr|0;}}}else{if(_1jr>=0){if(_1jq>=0){return E(_1js);}else{if(_1jr<=0){return E(_1js);}else{var _1ju=E(_1js);return (_1ju==0)?0:_1ju+_1jr|0;}}}else{var _1jv=E(_1js);return (_1jv==0)?0:_1jv+_1jr|0;}}},_1jw=(function(s){var ba = window['newByteArr'](16);ba['v']['w32'][0] = s[0];ba['v']['w32'][1] = s[1];ba['v']['w32'][2] = s[2];ba['v']['w32'][3] = s[3];return window['md51'](ba,16);}),_1jx=function(_1jy){var _1jz=function(_){return new F(function(){return E(_1jw)(E(_1jy));});};return new F(function(){return _3v(_1jz);});},_1jA=function(_1jB,_1jC,_1jD){while(1){var _1jE=(function(_1jF,_1jG,_1jH){if(_1jF>_1jG){var _1jI=_1jG,_1jJ=_1jF,_1jK=_1jH;_1jB=_1jI;_1jC=_1jJ;_1jD=_1jK;return null;}else{var _1jL=new T(function(){return B(_1jx(_1jH));}),_1jM=new T(function(){var _1jN=(_1jG-_1jF|0)+1|0;switch(_1jN){case -1:return _1jF;break;case 0:return E(_kb);break;default:var _1jO=function(_){var _1jP=E(_1jo)(E(_1jH));return new F(function(){return _1e(_1jP,0);});};return B(_1jp(B(_3v(_1jO)),_1jN))+_1jF|0;}});return [0,_1jM,_1jL];}})(_1jB,_1jC,_1jD);if(_1jE!=null){return _1jE;}}},_1jQ=(function(){var ba = window['newByteArr'](16);ba['v']['f64'][0] = Math.random();ba['v']['f64'][1] = Math.random();return window['md51'](ba,16);}),_1jR=function(_1jS,_){while(1){var _1jT=(function(_1jU,_){var _1jV=E(_1jU);if(!_1jV[0]){return _11;}else{var _1jW=_1jV[2],_1jX=E(_1jV[1]);if(!_1jX[0]){_1jS=_1jW;return null;}else{var _1jY=_1jX[2],_1jZ=E(_1jX[1]),_1k0=E(_1jZ[1]),_1k1=E(_1jZ[2]),_1k2=E(_1jQ),_1k3=_1k2(),_1k4=_1k3,_1k5=E(_1k1[2]),_1k6=E(_1k0[2]);if((_1k5-_1k6|0)<4){var _1k7=function(_1k8,_){var _1k9=E(_1k8);if(!_1k9[0]){return new F(function(){return _1jR(_1jW,_);});}else{var _1ka=_1k9[2],_1kb=E(_1k9[1]),_1kc=E(_1kb[1]),_1kd=E(_1kb[2]),_1ke=_1k2(),_1kf=_1ke,_1kg=E(_1kd[2]),_1kh=E(_1kc[2]);if((_1kg-_1kh|0)<4){var _1ki=B(_1k7(_1ka,_));return [1,_11,_1ki];}else{var _1kj=B(_1k7(_1ka,_)),_1kk=new T(function(){return E(B(_1jA((_1kh+2|0)+1|0,(_1kg-2|0)-1|0,_1kf))[1]);});return [1,[1,[0,_1kc,[0,_1kd[1],_1kk]],[1,[0,[0,_1kc[1],_1kk],_1kd],_11]],_1kj];}}},_1kl=B(_1k7(_1jY,_));return [1,_11,_1kl];}else{var _1km=function(_1kn,_){var _1ko=E(_1kn);if(!_1ko[0]){return new F(function(){return _1jR(_1jW,_);});}else{var _1kp=_1ko[2],_1kq=E(_1ko[1]),_1kr=E(_1kq[1]),_1ks=E(_1kq[2]),_1kt=_1k2(),_1ku=_1kt,_1kv=E(_1ks[2]),_1kw=E(_1kr[2]);if((_1kv-_1kw|0)<4){var _1kx=B(_1km(_1kp,_));return [1,_11,_1kx];}else{var _1ky=B(_1km(_1kp,_)),_1kz=new T(function(){return E(B(_1jA((_1kw+2|0)+1|0,(_1kv-2|0)-1|0,_1ku))[1]);});return [1,[1,[0,_1kr,[0,_1ks[1],_1kz]],[1,[0,[0,_1kr[1],_1kz],_1ks],_11]],_1ky];}}},_1kA=B(_1km(_1jY,_)),_1kB=new T(function(){return E(B(_1jA((_1k6+2|0)+1|0,(_1k5-2|0)-1|0,_1k4))[1]);});return [1,[1,[0,_1k0,[0,_1k1[1],_1kB]],[1,[0,[0,_1k0[1],_1kB],_1k1],_11]],_1kA];}}}})(_1jS,_);if(_1jT!=null){return _1jT;}}},_1kC=function(_1kD,_){var _1kE=E(_1kD);if(!_1kE[0]){return _11;}else{var _1kF=_1kE[2],_1kG=E(_1kE[1]),_1kH=E(_1kG[1]),_1kI=E(_1kG[2]),_1kJ=E(_1jQ),_1kK=_1kJ(),_1kL=_1kK,_1kM=E(_1kI[1]),_1kN=E(_1kH[1]);if((_1kM-_1kN|0)<4){var _1kO=function(_1kP,_){var _1kQ=E(_1kP);if(!_1kQ[0]){return _11;}else{var _1kR=_1kQ[2],_1kS=E(_1kQ[1]),_1kT=E(_1kS[1]),_1kU=E(_1kS[2]),_1kV=_1kJ(),_1kW=_1kV,_1kX=E(_1kU[1]),_1kY=E(_1kT[1]);if((_1kX-_1kY|0)<4){var _1kZ=B(_1kO(_1kR,_));return [1,_11,_1kZ];}else{var _1l0=B(_1kO(_1kR,_)),_1l1=new T(function(){return E(B(_1jA((_1kY+2|0)+1|0,(_1kX-2|0)-1|0,_1kW))[1]);});return [1,[1,[0,_1kT,[0,_1l1,_1kU[2]]],[1,[0,[0,_1l1,_1kT[2]],_1kU],_11]],_1l0];}}},_1l2=B(_1kO(_1kF,_));return [1,_11,_1l2];}else{var _1l3=function(_1l4,_){var _1l5=E(_1l4);if(!_1l5[0]){return _11;}else{var _1l6=_1l5[2],_1l7=E(_1l5[1]),_1l8=E(_1l7[1]),_1l9=E(_1l7[2]),_1la=_1kJ(),_1lb=_1la,_1lc=E(_1l9[1]),_1ld=E(_1l8[1]);if((_1lc-_1ld|0)<4){var _1le=B(_1l3(_1l6,_));return [1,_11,_1le];}else{var _1lf=B(_1l3(_1l6,_)),_1lg=new T(function(){return E(B(_1jA((_1ld+2|0)+1|0,(_1lc-2|0)-1|0,_1lb))[1]);});return [1,[1,[0,_1l8,[0,_1lg,_1l9[2]]],[1,[0,[0,_1lg,_1l8[2]],_1l9],_11]],_1lf];}}},_1lh=B(_1l3(_1kF,_)),_1li=new T(function(){return E(B(_1jA((_1kN+2|0)+1|0,(_1kM-2|0)-1|0,_1kL))[1]);});return [1,[1,[0,_1kH,[0,_1li,_1kI[2]]],[1,[0,[0,_1li,_1kH[2]],_1kI],_11]],_1lh];}}},_1lj=0,_1lk=[0,_1lj,_1lj],_1ll=34,_1lm=44,_1ln=[0,_1lm,_1ll],_1lo=[0,_1lk,_1ln],_1lp=[1,_1lo,_11],_1lq=function(_1lr,_){var _1ls=E(_1lr);if(_1ls==1){var _1lt=B(_1kC(_1lp,_)),_1lu=B(_1jR(_1lt,_)),_1lv=_1lu;return new T(function(){return B(_1jm(_1lv));});}else{var _1lw=B(_1lq(_1ls+1|0,_)),_1lx=B(_1kC(_1lw,_)),_1ly=B(_1jR(_1lx,_)),_1lz=_1ly;return new T(function(){return B(_1jm(_1lz));});}},_1lA=function(_1lB,_){var _1lC=E(_1lB);if(!_1lC[0]){return _11;}else{var _1lD=_1lC[2],_1lE=E(_1lC[1]),_1lF=E(_1lE[1]),_1lG=E(_1lE[2]),_1lH=E(_1jQ),_1lI=_1lH(),_1lJ=_1lI,_1lK=_1lH(),_1lL=_1lK,_1lM=_1lH(),_1lN=_1lM,_1lO=_1lH(),_1lP=_1lO,_1lQ=E(_1lF[1]),_1lR=E(_1lG[1]);if((_1lQ+1|0)>(_1lR-2|0)){var _1lS=function(_1lT,_){while(1){var _1lU=(function(_1lV,_){var _1lW=E(_1lV);if(!_1lW[0]){return _11;}else{var _1lX=_1lW[2],_1lY=E(_1lW[1]),_1lZ=E(_1lY[1]),_1m0=E(_1lY[2]),_1m1=_1lH(),_1m2=_1m1,_1m3=_1lH(),_1m4=_1m3,_1m5=_1lH(),_1m6=_1m5,_1m7=_1lH(),_1m8=_1m7,_1m9=E(_1lZ[1]),_1ma=E(_1m0[1]);if((_1m9+1|0)>(_1ma-2|0)){_1lT=_1lX;return null;}else{var _1mb=E(_1lZ[2]),_1mc=E(_1m0[2]);if((_1mb+1|0)>(_1mc-2|0)){_1lT=_1lX;return null;}else{var _1md=B(_1lS(_1lX,_)),_1me=new T(function(){return E(B(_1jA(_1m9+1|0,_1ma-2|0,_1m2))[1]);}),_1mf=new T(function(){return E(B(_1jA(_1mb+1|0,_1mc-2|0,_1m6))[1]);}),_1mg=new T(function(){return E(B(_1jA((E(_1mf)+2|0)-1|0,_1mc-1|0,_1m8))[1]);}),_1mh=new T(function(){return E(B(_1jA((E(_1me)+2|0)-1|0,_1ma-1|0,_1m4))[1]);});return [1,[0,[0,_1me,_1mf],[0,_1mh,_1mg]],_1md];}}}})(_1lT,_);if(_1lU!=null){return _1lU;}}};return new F(function(){return _1lS(_1lD,_);});}else{var _1mi=E(_1lF[2]),_1mj=E(_1lG[2]);if((_1mi+1|0)>(_1mj-2|0)){var _1mk=function(_1ml,_){while(1){var _1mm=(function(_1mn,_){var _1mo=E(_1mn);if(!_1mo[0]){return _11;}else{var _1mp=_1mo[2],_1mq=E(_1mo[1]),_1mr=E(_1mq[1]),_1ms=E(_1mq[2]),_1mt=_1lH(),_1mu=_1mt,_1mv=_1lH(),_1mw=_1mv,_1mx=_1lH(),_1my=_1mx,_1mz=_1lH(),_1mA=_1mz,_1mB=E(_1mr[1]),_1mC=E(_1ms[1]);if((_1mB+1|0)>(_1mC-2|0)){_1ml=_1mp;return null;}else{var _1mD=E(_1mr[2]),_1mE=E(_1ms[2]);if((_1mD+1|0)>(_1mE-2|0)){_1ml=_1mp;return null;}else{var _1mF=B(_1mk(_1mp,_)),_1mG=new T(function(){return E(B(_1jA(_1mB+1|0,_1mC-2|0,_1mu))[1]);}),_1mH=new T(function(){return E(B(_1jA(_1mD+1|0,_1mE-2|0,_1my))[1]);}),_1mI=new T(function(){return E(B(_1jA((E(_1mH)+2|0)-1|0,_1mE-1|0,_1mA))[1]);}),_1mJ=new T(function(){return E(B(_1jA((E(_1mG)+2|0)-1|0,_1mC-1|0,_1mw))[1]);});return [1,[0,[0,_1mG,_1mH],[0,_1mJ,_1mI]],_1mF];}}}})(_1ml,_);if(_1mm!=null){return _1mm;}}};return new F(function(){return _1mk(_1lD,_);});}else{var _1mK=function(_1mL,_){while(1){var _1mM=(function(_1mN,_){var _1mO=E(_1mN);if(!_1mO[0]){return _11;}else{var _1mP=_1mO[2],_1mQ=E(_1mO[1]),_1mR=E(_1mQ[1]),_1mS=E(_1mQ[2]),_1mT=_1lH(),_1mU=_1mT,_1mV=_1lH(),_1mW=_1mV,_1mX=_1lH(),_1mY=_1mX,_1mZ=_1lH(),_1n0=_1mZ,_1n1=E(_1mR[1]),_1n2=E(_1mS[1]);if((_1n1+1|0)>(_1n2-2|0)){_1mL=_1mP;return null;}else{var _1n3=E(_1mR[2]),_1n4=E(_1mS[2]);if((_1n3+1|0)>(_1n4-2|0)){_1mL=_1mP;return null;}else{var _1n5=B(_1mK(_1mP,_)),_1n6=new T(function(){return E(B(_1jA(_1n1+1|0,_1n2-2|0,_1mU))[1]);}),_1n7=new T(function(){return E(B(_1jA(_1n3+1|0,_1n4-2|0,_1mY))[1]);}),_1n8=new T(function(){return E(B(_1jA((E(_1n7)+2|0)-1|0,_1n4-1|0,_1n0))[1]);}),_1n9=new T(function(){return E(B(_1jA((E(_1n6)+2|0)-1|0,_1n2-1|0,_1mW))[1]);});return [1,[0,[0,_1n6,_1n7],[0,_1n9,_1n8]],_1n5];}}}})(_1mL,_);if(_1mM!=null){return _1mM;}}},_1na=B(_1mK(_1lD,_)),_1nb=new T(function(){return E(B(_1jA(_1lQ+1|0,_1lR-2|0,_1lJ))[1]);}),_1nc=new T(function(){return E(B(_1jA(_1mi+1|0,_1mj-2|0,_1lN))[1]);}),_1nd=new T(function(){return E(B(_1jA((E(_1nc)+2|0)-1|0,_1mj-1|0,_1lP))[1]);}),_1ne=new T(function(){return E(B(_1jA((E(_1nb)+2|0)-1|0,_1lR-1|0,_1lL))[1]);});return [1,[0,[0,_1nb,_1nc],[0,_1ne,_1nd]],_1na];}}}},_1nf=function(_1ng,_1nh,_){var _1ni=E(_1ng);if(!_1ni[0]){return _11;}else{var _1nj=_1ni[2],_1nk=E(_1nh);if(!_1nk[0]){return _11;}else{var _1nl=_1nk[2],_1nm=E(_1ni[1]),_1nn=E(_1nm[2]),_1no=E(_1nk[1]),_1np=E(_1no[1]),_1nq=_1np[1],_1nr=E(_1no[2])[1],_1ns=E(E(_1nm[1])[2]);if(!E(_1ns)){var _1nt=B(_1nf(_1nj,_1nl,_));return [1,_11,_1nt];}else{var _1nu=E(_1jQ),_1nv=_1nu(),_1nw=_1nv,_1nx=function(_1ny,_1nz,_){var _1nA=E(_1ny);if(!_1nA[0]){return _11;}else{var _1nB=_1nA[2],_1nC=E(_1nz);if(!_1nC[0]){return _11;}else{var _1nD=_1nC[2],_1nE=E(_1nA[1]),_1nF=E(_1nE[2]),_1nG=E(_1nC[1]),_1nH=E(_1nG[1]),_1nI=_1nH[1],_1nJ=E(_1nG[2])[1],_1nK=E(E(_1nE[1])[2]);if(!E(_1nK)){var _1nL=B(_1nx(_1nB,_1nD,_));return [1,_11,_1nL];}else{var _1nM=_1nu(),_1nN=_1nM,_1nO=B(_1nx(_1nB,_1nD,_)),_1nP=new T(function(){return E(B(_1jA(E(_1nI),E(_1nJ),_1nN))[1]);});return [1,[1,[0,[0,[0,_1nP,_1nK],[0,_1nP,_1nH[2]]],[0,_1nP,_1nK]],_11],_1nO];}}}},_1nQ=B(_1nx(_1nj,_1nl,_)),_1nR=new T(function(){return E(B(_1jA(E(_1nq),E(_1nr),_1nw))[1]);});return [1,[1,[0,[0,[0,_1nR,_1ns],[0,_1nR,_1np[2]]],[0,_1nR,_1ns]],_11],_1nQ];}}}},_1nS=function(_1nT,_1nU,_){var _1nV=E(_1nT);if(!_1nV[0]){return _11;}else{var _1nW=_1nV[2],_1nX=E(_1nU);if(!_1nX[0]){return _11;}else{var _1nY=_1nX[2],_1nZ=E(_1nV[1]),_1o0=E(_1nZ[1]),_1o1=E(_1nX[1]),_1o2=E(_1o1[1])[1],_1o3=E(_1o1[2]),_1o4=_1o3[1],_1o5=E(E(_1nZ[2])[2]);if(E(_1o5)==34){var _1o6=B(_1nS(_1nW,_1nY,_));return [1,_11,_1o6];}else{var _1o7=E(_1jQ),_1o8=_1o7(),_1o9=_1o8,_1oa=function(_1ob,_1oc,_){var _1od=E(_1ob);if(!_1od[0]){return _11;}else{var _1oe=_1od[2],_1of=E(_1oc);if(!_1of[0]){return _11;}else{var _1og=_1of[2],_1oh=E(_1od[1]),_1oi=E(_1oh[1]),_1oj=E(_1of[1]),_1ok=E(_1oj[1])[1],_1ol=E(_1oj[2]),_1om=_1ol[1],_1on=E(E(_1oh[2])[2]);if(E(_1on)==34){var _1oo=B(_1oa(_1oe,_1og,_));return [1,_11,_1oo];}else{var _1op=_1o7(),_1oq=_1op,_1or=B(_1oa(_1oe,_1og,_)),_1os=new T(function(){return E(B(_1jA(E(_1ok),E(_1om),_1oq))[1]);});return [1,[1,[0,[0,[0,_1os,_1ol[2]],[0,_1os,_1on]],[0,_1os,_1on]],_11],_1or];}}}},_1ot=B(_1oa(_1nW,_1nY,_)),_1ou=new T(function(){return E(B(_1jA(E(_1o2),E(_1o4),_1o9))[1]);});return [1,[1,[0,[0,[0,_1ou,_1o3[2]],[0,_1ou,_1o5]],[0,_1ou,_1o5]],_11],_1ot];}}}},_1ov=function(_1ow,_1ox,_){var _1oy=E(_1ow);if(!_1oy[0]){return _11;}else{var _1oz=_1oy[2],_1oA=E(_1ox);if(!_1oA[0]){return _11;}else{var _1oB=_1oA[2],_1oC=E(_1oy[1]),_1oD=E(_1oC[2]),_1oE=E(_1oA[1]),_1oF=E(_1oE[1]),_1oG=_1oF[2],_1oH=E(_1oE[2])[2],_1oI=E(E(_1oC[1])[1]);if(!E(_1oI)){var _1oJ=B(_1ov(_1oz,_1oB,_));return [1,_11,_1oJ];}else{var _1oK=E(_1jQ),_1oL=_1oK(),_1oM=_1oL,_1oN=function(_1oO,_1oP,_){var _1oQ=E(_1oO);if(!_1oQ[0]){return _11;}else{var _1oR=_1oQ[2],_1oS=E(_1oP);if(!_1oS[0]){return _11;}else{var _1oT=_1oS[2],_1oU=E(_1oQ[1]),_1oV=E(_1oU[2]),_1oW=E(_1oS[1]),_1oX=E(_1oW[1]),_1oY=_1oX[2],_1oZ=E(_1oW[2])[2],_1p0=E(E(_1oU[1])[1]);if(!E(_1p0)){var _1p1=B(_1oN(_1oR,_1oT,_));return [1,_11,_1p1];}else{var _1p2=_1oK(),_1p3=_1p2,_1p4=B(_1oN(_1oR,_1oT,_)),_1p5=new T(function(){return E(B(_1jA(E(_1oY),E(_1oZ),_1p3))[1]);});return [1,[1,[0,[0,[0,_1p0,_1p5],[0,_1oX[1],_1p5]],[0,_1p0,_1p5]],_11],_1p4];}}}},_1p6=B(_1oN(_1oz,_1oB,_)),_1p7=new T(function(){return E(B(_1jA(E(_1oG),E(_1oH),_1oM))[1]);});return [1,[1,[0,[0,[0,_1oI,_1p7],[0,_1oF[1],_1p7]],[0,_1oI,_1p7]],_11],_1p6];}}}},_1p8=function(_1p9,_1pa,_){var _1pb=E(_1p9);if(!_1pb[0]){return _11;}else{var _1pc=_1pb[2],_1pd=E(_1pa);if(!_1pd[0]){return _11;}else{var _1pe=_1pd[2],_1pf=E(_1pb[1]),_1pg=E(_1pf[1]),_1ph=E(_1pd[1]),_1pi=E(_1ph[1])[2],_1pj=E(_1ph[2]),_1pk=_1pj[2],_1pl=E(E(_1pf[2])[1]);if(E(_1pl)==44){var _1pm=B(_1p8(_1pc,_1pe,_));return [1,_11,_1pm];}else{var _1pn=E(_1jQ),_1po=_1pn(),_1pp=_1po,_1pq=function(_1pr,_1ps,_){var _1pt=E(_1pr);if(!_1pt[0]){return _11;}else{var _1pu=_1pt[2],_1pv=E(_1ps);if(!_1pv[0]){return _11;}else{var _1pw=_1pv[2],_1px=E(_1pt[1]),_1py=E(_1px[1]),_1pz=E(_1pv[1]),_1pA=E(_1pz[1])[2],_1pB=E(_1pz[2]),_1pC=_1pB[2],_1pD=E(E(_1px[2])[1]);if(E(_1pD)==44){var _1pE=B(_1pq(_1pu,_1pw,_));return [1,_11,_1pE];}else{var _1pF=_1pn(),_1pG=_1pF,_1pH=B(_1pq(_1pu,_1pw,_)),_1pI=new T(function(){return E(B(_1jA(E(_1pA),E(_1pC),_1pG))[1]);});return [1,[1,[0,[0,[0,_1pB[1],_1pI],[0,_1pD,_1pI]],[0,_1pD,_1pI]],_11],_1pH];}}}},_1pJ=B(_1pq(_1pc,_1pe,_)),_1pK=new T(function(){return E(B(_1jA(E(_1pi),E(_1pk),_1pp))[1]);});return [1,[1,[0,[0,[0,_1pj[1],_1pK],[0,_1pl,_1pK]],[0,_1pl,_1pK]],_11],_1pJ];}}}},_1pL=function(_1pM,_1pN,_1pO,_1pP,_1pQ){var _1pR=E(_1pM);if(_1pR==1){var _1pS=E(_1pQ);if(!_1pS[0]){return [0,[0,1,[0,_1pN,_1pO],_1pP,E(_5B),E(_5B)],_11,_11];}else{var _1pT=E(E(_1pS[1])[1]),_1pU=E(_1pT[1]);return (_1pN>=_1pU)?(_1pN!=_1pU)?[0,[0,1,[0,_1pN,_1pO],_1pP,E(_5B),E(_5B)],_11,_1pS]:(_1pO<E(_1pT[2]))?[0,[0,1,[0,_1pN,_1pO],_1pP,E(_5B),E(_5B)],_1pS,_11]:[0,[0,1,[0,_1pN,_1pO],_1pP,E(_5B),E(_5B)],_11,_1pS]:[0,[0,1,[0,_1pN,_1pO],_1pP,E(_5B),E(_5B)],_1pS,_11];}}else{var _1pV=B(_1pL(_1pR>>1,_1pN,_1pO,_1pP,_1pQ)),_1pW=_1pV[1],_1pX=_1pV[3],_1pY=E(_1pV[2]);if(!_1pY[0]){return [0,_1pW,_11,_1pX];}else{var _1pZ=E(_1pY[1]),_1q0=_1pZ[1],_1q1=_1pZ[2],_1q2=E(_1pY[2]);if(!_1q2[0]){var _1q3=new T(function(){return B(_6q(_1q0,_1q1,_1pW));});return [0,_1q3,_11,_1pX];}else{var _1q4=_1q2[2],_1q5=E(_1q2[1]),_1q6=_1q5[2],_1q7=E(_1q0),_1q8=E(_1q5[1]),_1q9=_1q8[2],_1qa=E(_1q7[1]),_1qb=E(_1q8[1]);if(_1qa>=_1qb){if(_1qa!=_1qb){return [0,_1pW,_11,_1pY];}else{var _1qc=E(_1q9);if(E(_1q7[2])<_1qc){var _1qd=B(_1pL(_1pR>>1,_1qb,_1qc,_1q6,_1q4)),_1qe=_1qd[1],_1qf=new T(function(){return B(_7V(_1q7,_1q1,_1pW,_1qe));});return [0,_1qf,_1qd[2],_1qd[3]];}else{return [0,_1pW,_11,_1pY];}}}else{var _1qg=B(_1qh(_1pR>>1,_1qb,_1q9,_1q6,_1q4)),_1qi=_1qg[1],_1qj=new T(function(){return B(_7V(_1q7,_1q1,_1pW,_1qi));});return [0,_1qj,_1qg[2],_1qg[3]];}}}}},_1qh=function(_1qk,_1ql,_1qm,_1qn,_1qo){var _1qp=E(_1qk);if(_1qp==1){var _1qq=E(_1qo);if(!_1qq[0]){return [0,[0,1,[0,_1ql,_1qm],_1qn,E(_5B),E(_5B)],_11,_11];}else{var _1qr=E(E(_1qq[1])[1]),_1qs=E(_1qr[1]);if(_1ql>=_1qs){if(_1ql!=_1qs){return [0,[0,1,[0,_1ql,_1qm],_1qn,E(_5B),E(_5B)],_11,_1qq];}else{var _1qt=E(_1qm);return (_1qt<E(_1qr[2]))?[0,[0,1,[0,_1ql,_1qt],_1qn,E(_5B),E(_5B)],_1qq,_11]:[0,[0,1,[0,_1ql,_1qt],_1qn,E(_5B),E(_5B)],_11,_1qq];}}else{return [0,[0,1,[0,_1ql,_1qm],_1qn,E(_5B),E(_5B)],_1qq,_11];}}}else{var _1qu=B(_1qh(_1qp>>1,_1ql,_1qm,_1qn,_1qo)),_1qv=_1qu[1],_1qw=_1qu[3],_1qx=E(_1qu[2]);if(!_1qx[0]){return [0,_1qv,_11,_1qw];}else{var _1qy=E(_1qx[1]),_1qz=_1qy[1],_1qA=_1qy[2],_1qB=E(_1qx[2]);if(!_1qB[0]){var _1qC=new T(function(){return B(_6q(_1qz,_1qA,_1qv));});return [0,_1qC,_11,_1qw];}else{var _1qD=_1qB[2],_1qE=E(_1qB[1]),_1qF=_1qE[2],_1qG=E(_1qz),_1qH=E(_1qE[1]),_1qI=_1qH[2],_1qJ=E(_1qG[1]),_1qK=E(_1qH[1]);if(_1qJ>=_1qK){if(_1qJ!=_1qK){return [0,_1qv,_11,_1qx];}else{var _1qL=E(_1qI);if(E(_1qG[2])<_1qL){var _1qM=B(_1pL(_1qp>>1,_1qK,_1qL,_1qF,_1qD)),_1qN=_1qM[1],_1qO=new T(function(){return B(_7V(_1qG,_1qA,_1qv,_1qN));});return [0,_1qO,_1qM[2],_1qM[3]];}else{return [0,_1qv,_11,_1qx];}}}else{var _1qP=B(_1qh(_1qp>>1,_1qK,_1qI,_1qF,_1qD)),_1qQ=_1qP[1],_1qR=new T(function(){return B(_7V(_1qG,_1qA,_1qv,_1qQ));});return [0,_1qR,_1qP[2],_1qP[3]];}}}}},_1qS=function(_1qT,_1qU){while(1){var _1qV=E(_1qU);if(!_1qV[0]){return E(_1qT);}else{var _1qW=E(_1qV[1]),_1qX=E(_1qW[1]),_1qY=B(_1j3(_1qX[1],_1qX[2],_1qW[2],_1qT));_1qU=_1qV[2];_1qT=_1qY;continue;}}},_1qZ=function(_1r0,_1r1,_1r2,_1r3,_1r4){return new F(function(){return _1qS(B(_1j3(_1r1,_1r2,_1r3,_1r0)),_1r4);});},_1r5=function(_1r6,_1r7,_1r8){var _1r9=E(_1r7),_1ra=E(_1r9[1]);return new F(function(){return _1qS(B(_1j3(_1ra[1],_1ra[2],_1r9[2],_1r6)),_1r8);});},_1rb=function(_1rc,_1rd,_1re){var _1rf=E(_1re);if(!_1rf[0]){return E(_1rd);}else{var _1rg=E(_1rf[1]),_1rh=_1rg[1],_1ri=_1rg[2],_1rj=E(_1rf[2]);if(!_1rj[0]){return new F(function(){return _6q(_1rh,_1ri,_1rd);});}else{var _1rk=_1rj[2],_1rl=E(_1rj[1]),_1rm=_1rl[2],_1rn=E(_1rh),_1ro=_1rn[2],_1rp=E(_1rl[1]),_1rq=_1rp[2],_1rr=E(_1rn[1]),_1rs=E(_1rp[1]),_1rt=function(_1ru){var _1rv=B(_1qh(_1rc,_1rs,_1rq,_1rm,_1rk)),_1rw=_1rv[1],_1rx=E(_1rv[3]);if(!_1rx[0]){return new F(function(){return _1rb(_1rc<<1,B(_7V(_1rn,_1ri,_1rd,_1rw)),_1rv[2]);});}else{return new F(function(){return _1r5(B(_7V(_1rn,_1ri,_1rd,_1rw)),_1rx[1],_1rx[2]);});}};if(_1rr>=_1rs){if(_1rr!=_1rs){return new F(function(){return _1qZ(_1rd,_1rr,_1ro,_1ri,_1rj);});}else{var _1ry=E(_1ro);if(_1ry<E(_1rq)){return new F(function(){return _1rt(_);});}else{return new F(function(){return _1qZ(_1rd,_1rr,_1ry,_1ri,_1rj);});}}}else{return new F(function(){return _1rt(_);});}}}},_1rz=function(_1rA,_1rB,_1rC,_1rD,_1rE,_1rF){var _1rG=E(_1rF);if(!_1rG[0]){return new F(function(){return _6q([0,_1rC,_1rD],_1rE,_1rB);});}else{var _1rH=_1rG[2],_1rI=E(_1rG[1]),_1rJ=_1rI[2],_1rK=E(_1rI[1]),_1rL=_1rK[2],_1rM=E(_1rK[1]),_1rN=function(_1rO){var _1rP=B(_1qh(_1rA,_1rM,_1rL,_1rJ,_1rH)),_1rQ=_1rP[1],_1rR=E(_1rP[3]);if(!_1rR[0]){return new F(function(){return _1rb(_1rA<<1,B(_7V([0,_1rC,_1rD],_1rE,_1rB,_1rQ)),_1rP[2]);});}else{return new F(function(){return _1r5(B(_7V([0,_1rC,_1rD],_1rE,_1rB,_1rQ)),_1rR[1],_1rR[2]);});}};if(_1rC>=_1rM){if(_1rC!=_1rM){return new F(function(){return _1qZ(_1rB,_1rC,_1rD,_1rE,_1rG);});}else{if(_1rD<E(_1rL)){return new F(function(){return _1rN(_);});}else{return new F(function(){return _1qZ(_1rB,_1rC,_1rD,_1rE,_1rG);});}}}else{return new F(function(){return _1rN(_);});}}},_1rS=function(_1rT,_1rU,_1rV,_1rW,_1rX,_1rY){var _1rZ=E(_1rY);if(!_1rZ[0]){return new F(function(){return _6q([0,_1rV,_1rW],_1rX,_1rU);});}else{var _1s0=_1rZ[2],_1s1=E(_1rZ[1]),_1s2=_1s1[2],_1s3=E(_1s1[1]),_1s4=_1s3[2],_1s5=E(_1s3[1]),_1s6=function(_1s7){var _1s8=B(_1qh(_1rT,_1s5,_1s4,_1s2,_1s0)),_1s9=_1s8[1],_1sa=E(_1s8[3]);if(!_1sa[0]){return new F(function(){return _1rb(_1rT<<1,B(_7V([0,_1rV,_1rW],_1rX,_1rU,_1s9)),_1s8[2]);});}else{return new F(function(){return _1r5(B(_7V([0,_1rV,_1rW],_1rX,_1rU,_1s9)),_1sa[1],_1sa[2]);});}};if(_1rV>=_1s5){if(_1rV!=_1s5){return new F(function(){return _1qZ(_1rU,_1rV,_1rW,_1rX,_1rZ);});}else{var _1sb=E(_1rW);if(_1sb<E(_1s4)){return new F(function(){return _1s6(_);});}else{return new F(function(){return _1qZ(_1rU,_1rV,_1sb,_1rX,_1rZ);});}}}else{return new F(function(){return _1s6(_);});}}},_1sc=function(_1sd){var _1se=E(_1sd);if(!_1se[0]){return [1];}else{var _1sf=E(_1se[1]),_1sg=_1sf[1],_1sh=_1sf[2],_1si=E(_1se[2]);if(!_1si[0]){return [0,1,E(_1sg),_1sh,E(_5B),E(_5B)];}else{var _1sj=_1si[2],_1sk=E(_1si[1]),_1sl=_1sk[2],_1sm=E(_1sg),_1sn=E(_1sk[1]),_1so=_1sn[2],_1sp=E(_1sm[1]),_1sq=E(_1sn[1]);if(_1sp>=_1sq){if(_1sp!=_1sq){return new F(function(){return _1qZ([0,1,E(_1sm),_1sh,E(_5B),E(_5B)],_1sq,_1so,_1sl,_1sj);});}else{var _1sr=E(_1so);if(E(_1sm[2])<_1sr){return new F(function(){return _1rz(1,[0,1,E(_1sm),_1sh,E(_5B),E(_5B)],_1sq,_1sr,_1sl,_1sj);});}else{return new F(function(){return _1qZ([0,1,E(_1sm),_1sh,E(_5B),E(_5B)],_1sq,_1sr,_1sl,_1sj);});}}}else{return new F(function(){return _1rS(1,[0,1,E(_1sm),_1sh,E(_5B),E(_5B)],_1sq,_1so,_1sl,_1sj);});}}}},_1ss=new T(function(){return B(_wo(0,34));}),_1st=function(_1su){var _1sv=_1su,_1sw=new T(function(){var _1sx=E(_1su);if(_1sx==44){return [0];}else{return B(_1st(_1sx+1|0));}}),_1sy=function(_1sz){var _1sA=E(_1sz);if(!_1sA[0]){return E(_1sw);}else{var _1sB=_1sA[2],_1sC=new T(function(){return B(_1sy(_1sB));});return [1,[0,_1sv,_1sA[1]],_1sC];}};return new F(function(){return _1sy(_1ss);});},_1sD=new T(function(){return B(_1st(0));}),_1sE=32,_1sF=new T(function(){return [1,_1sE,_1sF];}),_1sG=new T(function(){return B(_NT(_1sD,_1sF));}),_1sH=new T(function(){return B(_1sc(_1sG));}),_1sI=35,_1sJ=function(_1sK){return E(E(_1sK)[1]);},_1sL=function(_1sM){var _1sN=E(_1sM);if(!_1sN[0]){return [0];}else{var _1sO=_1sN[2],_1sP=new T(function(){return B(_1sL(_1sO));},1);return new F(function(){return _v(_1sN[1],_1sP);});}},_1sQ=function(_1sR){return new F(function(){return _mW("Dungeon.hs:(127,5)-(128,21)|function tup");});},_1sS=new T(function(){return B(_1sQ(_));}),_1sT=function(_1sU){var _1sV=E(_1sU);if(!_1sV[0]){return E(_1sS);}else{var _1sW=_1sV[1],_1sX=E(_1sV[2]);return (_1sX[0]==0)?[0,_1sW,_1sW]:(E(_1sX[2])[0]==0)?[0,_1sW,_1sX[1]]:E(_1sS);}},_1sY=function(_1sZ,_1t0){return new F(function(){return _5b(E(E(_1sZ)[2]),E(E(_1t0)[2]));});},_1t1=function(_1t2){var _1t3=E(_1t2);if(!_1t3[0]){return [0];}else{var _1t4=_1t3[2],_1t5=new T(function(){return B(_1t1(_1t4));}),_1t6=function(_1t7){var _1t8=E(_1t7);if(!_1t8[0]){return E(_1t5);}else{var _1t9=_1t8[1],_1ta=_1t8[2],_1tb=new T(function(){return B(_1t6(_1ta));}),_1tc=new T(function(){return B(_1sT(_1t9));});return [1,_1tc,_1tb];}};return new F(function(){return _1t6(B(_1iU(2,B(_hR(_1sY,_1t3[1])))));});}},_1td=function(_1te,_1tf){var _1tg=E(_1tf);if(!_1tg[0]){return [0];}else{var _1th=_1tg[1],_1ti=_1tg[2],_1tj=new T(function(){var _1tk=new T(function(){return B(A(_1te,[_1th]));}),_1tl=B(_mw(_1tk,_1ti));return [0,_1tl[1],_1tl[2]];}),_1tm=new T(function(){return B(_1td(_1te,E(_1tj)[2]));}),_1tn=new T(function(){return E(E(_1tj)[1]);});return [1,[1,_1th,_1tn],_1tm];}},_1to=function(_1tp,_1tq){return E(E(_1tp)[1])==E(E(_1tq)[1]);},_1tr=function(_1ts,_1tt){return new F(function(){return _5b(E(E(_1ts)[1]),E(E(_1tt)[1]));});},_1tu=45,_1tv=function(_1tw,_1tx){return E(E(_1tw)[2])==E(E(_1tx)[2]);},_1ty=function(_1tz,_1tA,_1tB,_1tC){var _1tD=E(_1tC);if(!_1tD[0]){var _1tE=_1tD[3],_1tF=_1tD[4],_1tG=_1tD[5],_1tH=E(_1tD[2]),_1tI=E(_1tH[1]);if(_1tz>=_1tI){if(_1tz!=_1tI){return new F(function(){return _5G(_1tH,_1tE,_1tF,B(_1ty(_1tz,_1tA,_1tB,_1tG)));});}else{var _1tJ=E(_1tH[2]);if(_1tA>=_1tJ){if(_1tA!=_1tJ){return new F(function(){return _5G(_1tH,_1tE,_1tF,B(_1ty(_1tz,_1tA,_1tB,_1tG)));});}else{return [0,_1tD[1],[0,_1tz,_1tA],_1tB,E(_1tF),E(_1tG)];}}else{return new F(function(){return _6z(_1tH,_1tE,B(_1ty(_1tz,_1tA,_1tB,_1tF)),_1tG);});}}}else{return new F(function(){return _6z(_1tH,_1tE,B(_1ty(_1tz,_1tA,_1tB,_1tF)),_1tG);});}}else{return [0,1,[0,_1tz,_1tA],_1tB,E(_5B),E(_5B)];}},_1tK=function(_1tL,_1tM,_1tN,_1tO){var _1tP=E(_1tO);if(!_1tP[0]){var _1tQ=_1tP[3],_1tR=_1tP[4],_1tS=_1tP[5],_1tT=E(_1tP[2]),_1tU=E(_1tT[1]);if(_1tL>=_1tU){if(_1tL!=_1tU){return new F(function(){return _5G(_1tT,_1tQ,_1tR,B(_1tK(_1tL,_1tM,_1tN,_1tS)));});}else{var _1tV=E(_1tM),_1tW=E(_1tT[2]);if(_1tV>=_1tW){if(_1tV!=_1tW){return new F(function(){return _5G(_1tT,_1tQ,_1tR,B(_1ty(_1tL,_1tV,_1tN,_1tS)));});}else{return [0,_1tP[1],[0,_1tL,_1tV],_1tN,E(_1tR),E(_1tS)];}}else{return new F(function(){return _6z(_1tT,_1tQ,B(_1ty(_1tL,_1tV,_1tN,_1tR)),_1tS);});}}}else{return new F(function(){return _6z(_1tT,_1tQ,B(_1tK(_1tL,_1tM,_1tN,_1tR)),_1tS);});}}else{return [0,1,[0,_1tL,_1tM],_1tN,E(_5B),E(_5B)];}},_1tX=function(_1tY,_1tZ,_1u0){var _1u1=new T(function(){return [1,_1tY,_1u1];}),_1u2=function(_1u3){var _1u4=E(_1u3);if(!_1u4[0]){return E(_1u0);}else{var _1u5=E(_1u4[1]),_1u6=E(_1u5[1]),_1u7=E(_1u5[2]),_1u8=E(_1u6[1]),_1u9=E(_1u7[1]),_1ua=B(_1u2(_1u4[2]));if(_1u8<=_1u9){var _1ub=B(_wo(E(_1u6[2]),E(_1u7[2]))),_1uc=function(_1ud,_1ue){var _1uf=new T(function(){return _1ud==_1u9;}),_1ug=function(_1uh,_1ui){var _1uj=E(_1uh);if(!_1uj[0]){if(!E(_1uf)){return new F(function(){return _1uc(_1ud+1|0,_1ui);});}else{return E(_1ua);}}else{var _1uk=E(_1ui);if(!_1uk[0]){return E(_1ua);}else{return new F(function(){return _1tK(_1ud,_1uj[1],_1uk[1],B(_1ug(_1uj[2],_1uk[2])));});}}};return new F(function(){return _1ug(_1ub,_1ue);});};return new F(function(){return _1uc(_1u8,_1u1);});}else{return E(_1ua);}}};return new F(function(){return _1u2(_1tZ);});},_1ul=function(_1um){return E(E(_1um)[2]);},_1un=function(_){var _1uo=B(_1lq(0,_)),_1up=B(_1lA(_1uo,_)),_1uq=_1up,_1ur=B(_1nf(_1uo,_1uq,_)),_1us=_1ur,_1ut=B(_1nS(_1uo,_1uq,_)),_1uu=_1ut,_1uv=B(_1ov(_1uo,_1uq,_)),_1uw=_1uv,_1ux=B(_1p8(_1uo,_1uq,_)),_1uy=_1ux;return new T(function(){var _1uz=new T(function(){var _1uA=new T(function(){var _1uB=new T(function(){return B(_1sL(_1uy));}),_1uC=function(_1uD){var _1uE=E(_1uD);if(!_1uE[0]){return E(_1uB);}else{var _1uF=_1uE[2],_1uG=new T(function(){return B(_1uC(_1uF));},1);return new F(function(){return _v(_1uE[1],_1uG);});}};return B(_1uC(_1uw));}),_1uH=function(_1uI){var _1uJ=E(_1uI);if(!_1uJ[0]){return E(_1uA);}else{var _1uK=_1uJ[2],_1uL=new T(function(){return B(_1uH(_1uK));},1);return new F(function(){return _v(_1uJ[1],_1uL);});}};return B(_1uH(_1uu));}),_1uM=function(_1uN){var _1uO=E(_1uN);if(!_1uO[0]){return E(_1uz);}else{var _1uP=_1uO[2],_1uQ=new T(function(){return B(_1uM(_1uP));},1);return new F(function(){return _v(_1uO[1],_1uQ);});}},_1uR=B(_1uM(_1us)),_1uS=B(_wI(_1sJ,_1uR)),_1uT=new T(function(){return B(_wI(_1ul,_1uR));}),_1uU=new T(function(){var _1uV=function(_1uW){while(1){var _1uX=(function(_1uY){var _1uZ=E(_1uY);if(!_1uZ[0]){return [0];}else{var _1v0=_1uZ[2],_1v1=E(_1uZ[1]),_1v2=E(_1v1[1]),_1v3=E(_1v1[2]);if(E(_1v2[2])!=E(_1v3[2])){_1uW=_1v0;return null;}else{var _1v4=new T(function(){return B(_1uV(_1v0));}),_1v5=new T(function(){if(!B(_11X(_pI,_1v2,_1uT))){return E(_1v3);}else{return E(_1v2);}});return [1,_1v5,_1v4];}}})(_1uW);if(_1uX!=null){return _1uX;}}};return B(_1t1(B(_1td(_1to,B(_hR(_1tr,B(_1uV(_1uS))))))));}),_1v6=function(_1v7){var _1v8=E(_1v7);if(!_1v8[0]){return E(_1uU);}else{var _1v9=_1v8[2],_1va=new T(function(){return B(_1v6(_1v9));}),_1vb=function(_1vc){var _1vd=E(_1vc);if(!_1vd[0]){return E(_1va);}else{var _1ve=_1vd[1],_1vf=_1vd[2],_1vg=new T(function(){return B(_1vb(_1vf));}),_1vh=new T(function(){return B(_1sT(_1ve));});return [1,_1vh,_1vg];}};return new F(function(){return _1vb(B(_1iU(2,B(_hR(_1tr,_1v8[1])))));});}},_1vi=function(_1vj){while(1){var _1vk=(function(_1vl){var _1vm=E(_1vl);if(!_1vm[0]){return [0];}else{var _1vn=_1vm[2],_1vo=E(_1vm[1]),_1vp=E(_1vo[1]),_1vq=E(_1vo[2]);if(E(_1vp[1])!=E(_1vq[1])){_1vj=_1vn;return null;}else{var _1vr=new T(function(){return B(_1vi(_1vn));}),_1vs=new T(function(){if(!B(_11X(_pI,_1vp,_1uT))){return E(_1vq);}else{return E(_1vp);}});return [1,_1vs,_1vr];}}})(_1vj);if(_1vk!=null){return _1vk;}}},_1vt=B(_1tX(_1sI,_1uq,B(_1tX(_1tu,_1uS,B(_1tX(_1tu,B(_1v6(B(_1td(_1tv,B(_hR(_1sY,B(_1vi(_1uS)))))))),_1sH)))))),_1vu=function(_1vv){var _1vw=E(_1vv);if(!_1vw[0]){return E(_1vt);}else{var _1vx=_1vw[2],_1vy=E(_1vw[1]),_1vz=E(_1vy[1]),_1vA=E(_1vy[2]);if(!B(_11X(_pI,_1vz,_1uT))){return new F(function(){return _1j3(_1vz[1],_1vz[2],_1sI,B(_1vu(_1vx)));});}else{return new F(function(){return _1j3(_1vA[1],_1vA[2],_1sI,B(_1vu(_1vx)));});}}};return B(_1vu(_1uS));});},_1vB=new T(function(){return B(unCStr("    <div class=\"progress\">"));}),_1vC=new T(function(){return B(unCStr("  <div class=\"col-md-8\">"));}),_1vD=new T(function(){return B(unCStr("<div class=\"row\">"));}),_1vE=function(_1vF){var _1vG=E(_1vF);if(!_1vG[0]){return [0];}else{var _1vH=_1vG[2],_1vI=new T(function(){return B(_1vE(_1vH));},1);return new F(function(){return _v(_1vG[1],_1vI);});}},_1vJ=function(_1vK,_1vL){var _1vM=new T(function(){return B(_1vE(_1vL));},1);return new F(function(){return _v(_1vK,_1vM);});},_1vN=new T(function(){return B(unCStr("</div>"));}),_1vO=[1,_1vN,_11],_1vP=new T(function(){return B(unCStr("  </div>"));}),_1vQ=[1,_1vP,_1vO],_1vR=new T(function(){return B(unCStr("    </div>"));}),_1vS=new T(function(){return B(_1vJ(_1vR,_1vQ));}),_1vT=new T(function(){return B(unAppCStr("%;\"></div>",_1vS));}),_1vU=function(_1vV){var _1vW=E(_1vV);if(!_1vW[0]){return [0];}else{var _1vX=_1vW[2],_1vY=new T(function(){return B(_1vU(_1vX));},1);return new F(function(){return _v(_1vW[1],_1vY);});}},_1vZ=function(_1w0,_1w1){var _1w2=new T(function(){return B(_1vU(_1w1));},1);return new F(function(){return _v(_1w0,_1w2);});},_1w3=new T(function(){return B(unCStr("      \u7279\u6b8a\u9663\u55b6\u30fb\u30c7\u30c3\u30ad\u62e1\u5f35\u30fb\u738b\u306e\u529b"));}),_1w4=[1,_1vN,_1vO],_1w5=[1,_1vN,_1w4],_1w6=[1,_1vP,_1w5],_1w7=new T(function(){return B(unCStr("    <div id=\"join-party-btn\"></div>"));}),_1w8=[1,_1w7,_1w6],_1w9=new T(function(){return B(unCStr("    </p>"));}),_1wa=[1,_1w9,_1w8],_1wb=[1,_1w3,_1wa],_1wc=new T(function(){return B(unCStr("      <strong>\u56fa\u6709\u30b9\u30ad\u30eb</strong><br>"));}),_1wd=[1,_1wc,_1wb],_1we=new T(function(){return B(unCStr("    <p>"));}),_1wf=new T(function(){return B(_1vZ(_1we,_1wd));}),_1wg=function(_1wh,_1wi){var _1wj=E(_1wh);if(!_1wj[0]){return E(_1wf);}else{var _1wk=_1wj[1],_1wl=_1wj[2],_1wm=E(_1wi);if(!_1wm[0]){return E(_1wf);}else{var _1wn=_1wm[1],_1wo=_1wm[2],_1wp=new T(function(){return B(_1wg(_1wl,_1wo));},1),_1wq=new T(function(){var _1wr=new T(function(){var _1ws=new T(function(){var _1wt=new T(function(){var _1wu=new T(function(){var _1wv=new T(function(){var _1ww=new T(function(){return B(_v(B(_H(0,E(_1wn),_11)),_1vT));});return B(unAppCStr("      <div class=\"progress-bar\" role=\"progressbar\" style=\"width: ",_1ww));},1);return B(_v(_1vB,_1wv));},1);return B(_v(_1vC,_1wu));});return B(unAppCStr("</div>",_1wt));},1);return B(_v(_1wk,_1ws));});return B(unAppCStr("  <div class=\"col-md-3\">",_1wr));},1);return new F(function(){return _v(B(_v(_1vD,_1wq)),_1wp);});}}},_1wx=function(_1wy,_1wz,_1wA,_1wB){var _1wC=new T(function(){return B(_1wg(_1wz,_1wB));},1),_1wD=new T(function(){var _1wE=new T(function(){var _1wF=new T(function(){var _1wG=new T(function(){var _1wH=new T(function(){var _1wI=new T(function(){var _1wJ=new T(function(){return B(_v(B(_H(0,E(_1wA),_11)),_1vT));});return B(unAppCStr("      <div class=\"progress-bar\" role=\"progressbar\" style=\"width: ",_1wJ));},1);return B(_v(_1vB,_1wI));},1);return B(_v(_1vC,_1wH));});return B(unAppCStr("</div>",_1wG));},1);return B(_v(_1wy,_1wF));});return B(unAppCStr("  <div class=\"col-md-3\">",_1wE));},1);return new F(function(){return _v(B(_v(_1vD,_1wD)),_1wC);});},_1wK=new T(function(){return B(unCStr("MP"));}),_1wL=[1,_1wK,_11],_1wM=new T(function(){return B(unCStr("HP"));}),_1wN=[1,_1wM,_1wL],_1wO=new T(function(){return B(unCStr("LV"));}),_1wP=[1,_1wO,_1wN],_1wQ=new T(function(){return B(unCStr("LUC"));}),_1wR=[1,_1wQ,_1wP],_1wS=new T(function(){return B(unCStr("AGI"));}),_1wT=[1,_1wS,_1wR],_1wU=new T(function(){return B(unCStr("VIT"));}),_1wV=[1,_1wU,_1wT],_1wW=new T(function(){return B(unCStr("TEC"));}),_1wX=[1,_1wW,_1wV],_1wY=new T(function(){return B(unCStr("INT"));}),_1wZ=[1,_1wY,_1wX],_1x0=new T(function(){return B(unCStr("STR"));}),_1x1=new T(function(){return B(unCStr("  <div class=\"panel-body\">"));}),_1x2=[1,_1x1,_11],_1x3=[1,_1vP,_1x2],_1x4=new T(function(){return B(unCStr("    </h3>"));}),_1x5=new T(function(){return B(unCStr("    <h3 class=\"panel-title\">"));}),_1x6=new T(function(){return B(unCStr("  <div class=\"panel-heading\">"));}),_1x7=new T(function(){return B(unCStr("<div class=\"panel panel-default\">"));}),_1x8=function(_1x9){var _1xa=new T(function(){var _1xb=E(_1x9),_1xc=_1xb[1],_1xd=_1xb[2],_1xe=_1xb[3],_1xf=_1xb[4],_1xg=_1xb[5],_1xh=_1xb[6],_1xi=_1xb[7],_1xj=_1xb[8],_1xk=_1xb[9],_1xl=_1xb[11],_1xm=new T(function(){var _1xn=new T(function(){var _1xo=new T(function(){var _1xp=new T(function(){var _1xq=new T(function(){var _1xr=new T(function(){var _1xs=new T(function(){var _1xt=new T(function(){var _1xu=new T(function(){return B(_1wx(_1x0,_1wZ,_1xd,[1,_1xe,[1,_1xf,[1,_1xg,[1,_1xh,[1,_1xi,[1,_1xj,[1,_1xk,[1,_1xl,_11]]]]]]]]));}),_1xv=function(_1xw){var _1xx=E(_1xw);if(!_1xx[0]){return E(_1xu);}else{var _1xy=_1xx[2],_1xz=new T(function(){return B(_1xv(_1xy));},1);return new F(function(){return _v(_1xx[1],_1xz);});}},_1xA=function(_1xB,_1xC){var _1xD=new T(function(){return B(_1xv(_1xC));},1);return new F(function(){return _v(_1xB,_1xD);});};return B(_1xA(_1x4,_1x3));});return B(unAppCStr("(<a data-toggle=\"modal\" data-target=\"#myModal\"> S </a> )",_1xt));},1);return B(_v(_1xc,_1xs));});return B(unAppCStr("      ",_1xr));},1);return B(_v(_1x5,_1xq));},1);return B(_v(_1x6,_1xp));},1);return B(_v(_1x7,_1xo));});return B(unAppCStr("\">",_1xn));},1);return B(_v(_1xc,_1xm));});return new F(function(){return unAppCStr("<div class=\"col-md-4 career\" id=\"character-detail-",_1xa);});},_1xE=function(_1xF,_1xG){return new F(function(){return _bH(_1xF,E(_1xG));});},_1xH=new T(function(){return B(unCStr("Map.!: given key is not an element in the map"));}),_1xI=new T(function(){return B(err(_1xH));}),_1xJ=function(_1xK,_1xL,_1xM){while(1){var _1xN=E(_1xM);if(!_1xN[0]){var _1xO=_1xN[4],_1xP=_1xN[5],_1xQ=E(_1xN[2]),_1xR=E(_1xQ[1]);if(_1xK>=_1xR){if(_1xK!=_1xR){_1xM=_1xP;continue;}else{var _1xS=E(_1xQ[2]);if(_1xL>=_1xS){if(_1xL!=_1xS){_1xM=_1xP;continue;}else{return E(_1xN[3]);}}else{_1xM=_1xO;continue;}}}else{_1xM=_1xO;continue;}}else{return E(_1xI);}}},_1xT=function(_1xU,_1xV,_1xW){while(1){var _1xX=E(_1xW);if(!_1xX[0]){var _1xY=_1xX[4],_1xZ=_1xX[5],_1y0=E(_1xX[2]),_1y1=E(_1y0[1]);if(_1xU>=_1y1){if(_1xU!=_1y1){_1xW=_1xZ;continue;}else{var _1y2=E(_1xV),_1y3=E(_1y0[2]);if(_1y2>=_1y3){if(_1y2!=_1y3){return new F(function(){return _1xJ(_1xU,_1y2,_1xZ);});}else{return E(_1xX[3]);}}else{return new F(function(){return _1xJ(_1xU,_1y2,_1xY);});}}}else{_1xW=_1xY;continue;}}else{return E(_1xI);}}},_1y4=new T(function(){return B(_wo(0,20));}),_1y5=function(_1y6,_){var _1y7=E(_1jQ)(),_1y8=_1y7;return new T(function(){var _1y9=function(_1ya){var _1yb=E(_1ya);if(!_1yb[0]){return [0];}else{var _1yc=_1yb[2],_1yd=new T(function(){return B(_1y9(_1yc));}),_1ye=E(_1y4);if(!_1ye[0]){return E(_1yd);}else{var _1yf=_1ye[1],_1yg=_1ye[2],_1yh=E(_1yb[1]),_1yi=_1yh;if(E(B(_1xT(_1yi,_1yf,_1y6)))==35){var _1yj=new T(function(){var _1yk=function(_1yl){while(1){var _1ym=(function(_1yn){var _1yo=E(_1yn);if(!_1yo[0]){return E(_1yd);}else{var _1yp=_1yo[1],_1yq=_1yo[2];if(E(B(_1xT(_1yi,_1yp,_1y6)))==35){var _1yr=new T(function(){return B(_1yk(_1yq));});return [1,[0,_1yh,_1yp],_1yr];}else{_1yl=_1yq;return null;}}})(_1yl);if(_1ym!=null){return _1ym;}}};return B(_1yk(_1yg));});return [1,[0,_1yh,_1yf],_1yj];}else{var _1ys=function(_1yt){while(1){var _1yu=(function(_1yv){var _1yw=E(_1yv);if(!_1yw[0]){return E(_1yd);}else{var _1yx=_1yw[1],_1yy=_1yw[2];if(E(B(_1xT(_1yi,_1yx,_1y6)))==35){var _1yz=new T(function(){return B(_1ys(_1yy));});return [1,[0,_1yh,_1yx],_1yz];}else{_1yt=_1yy;return null;}}})(_1yt);if(_1yu!=null){return _1yu;}}};return new F(function(){return _1ys(_1yg);});}}}},_1yA=B(_1y9(_1y4));return B(_1xE(_1yA,B(_1jA(0,B(_NK(_1yA,0))-1|0,_1y8))[1]));});},_1yB=46,_1yC=new T(function(){return [1,_1yB,_1yC];}),_1yD=new T(function(){return B(_NT(_1sD,_1yC));}),_1yE=new T(function(){return B(_1sc(_1yD));}),_1yF=0,_1yG=new T(function(){return B(unCStr("\u30c7\u30d3\u30eb\u30a8\u30f3\u30da\u30e9\u30fc"));}),_1yH=[1,_1e0,_11],_1yI=[1,_1e0,_1yH],_1yJ=[1,_1e0,_1yI],_1yK=new T(function(){return B(_NT(_NS,_1yJ));}),_1yL=new T(function(){return B(_O2(_NR,_1yK));}),_1yM=new T(function(){return B(_NK(_1yJ,0));}),_1yN=[0,_Oa,_1yM,_1yL],_1yO=100,_1yP=[0,_1yG,_Oo,_Oo,_Oo,_On,_Op,_Oc,_Od,_1yO,_1yO,_Op,_Op,_1yN],_1yQ=[1,_1yP,_11],_1yR=[0,_Pc,_OF,_OE,_Op,_OG,_Oc,_On,_Od,_Oe,_Oe,_Oo,_Oo,_Ob],_1yS=[1,_1yR,_11],_1yT=[1,_P7,_1yS],_1yU=[1,_Pb,_1yT],_1yV=new T(function(){return B(unCStr("\u30d7\u30ea\u30f3\u30bb\u30b9"));}),_1yW=[1,_1e0,_11],_1yX=new T(function(){return B(_NT(_NS,_1yW));}),_1yY=new T(function(){return B(_O2(_NR,_1yX));}),_1yZ=new T(function(){return B(_NK(_1yW,0));}),_1z0=[0,_Oa,_1yZ,_1yY],_1z1=[0,_1yV,_1z0],_1z2=[1,_1z1,_11],_1z3=new T(function(){return B(_9s(_1z2));}),_1z4=[0,_wf,_1z3],_1z5=[1,_1z4,_11],_1z6=new T(function(){return B(_O2(_NR,_1z5));}),_1z7=[0,_1yU,_1yQ,_wf,_1z6,_1yF],_1z8=function(_1z9){var _1za=new T(function(){var _1zb=E(_1z9);if(_1zb==255){return [0];}else{var _1zc=B(_1z8(_1zb+1|0));return [1,_1zc[1],_1zc[2]];}});return [0,[0,_1z9,_125],_1za];},_1zd=new T(function(){var _1ze=B(_1z8(0));return B(_O2(_NR,[1,_1ze[1],_1ze[2]]));}),_1zf=function(_1zg,_1zh){var _1zi=E(_1zg);if(!_1zi[0]){return [0];}else{var _1zj=_1zi[1],_1zk=_1zi[2],_1zl=E(_1zh);if(!_1zl[0]){return [0];}else{var _1zm=_1zl[2],_1zn=new T(function(){return B(_1zf(_1zk,_1zm));}),_1zo=new T(function(){return E(E(_1zj)[1]);});return [1,[0,_1zo,_1zl[1]],_1zn];}}},_1zp=function(_1zq,_1zr){var _1zs=E(_1zq);if(!_1zs[0]){return [0];}else{var _1zt=_1zs[1],_1zu=_1zs[2],_1zv=E(_1zr);if(!_1zv[0]){return [0];}else{var _1zw=_1zv[2],_1zx=new T(function(){return B(_1zp(_1zu,_1zw));}),_1zy=new T(function(){return E(E(_1zt)[1]);});return [1,[0,_1zy,_1zv[1]],_1zx];}}},_1zz=(function(e,c) {return e.classList.contains(c);}),_1zA=function(_1zB,_1zC){while(1){var _1zD=(function(_1zE,_1zF){var _1zG=E(_1zF);switch(_1zG[0]){case 0:var _1zH=_1zG[4],_1zI=new T(function(){return B(_1zA(_1zE,_1zH));});_1zB=_1zI;_1zC=_1zG[3];return null;case 1:return [1,_1zG[1],_1zE];default:return E(_1zE);}})(_1zB,_1zC);if(_1zD!=null){return _1zD;}}},_1zJ=function(_1zK){var _1zL=E(_1zK);if(!_1zL[0]){var _1zM=_1zL[3],_1zN=_1zL[4];if(_1zL[2]>=0){var _1zO=new T(function(){return B(_1zA(_11,_1zN));});return new F(function(){return _1zA(_1zO,_1zM);});}else{var _1zP=new T(function(){return B(_1zA(_11,_1zM));});return new F(function(){return _1zA(_1zP,_1zN);});}}else{return new F(function(){return _1zA(_11,_1zL);});}},_1zQ=new T(function(){return B(unCStr("tactic-current-detail"));}),_1zR=[1,_lA,_1zQ],_1zS=new T(function(){return B(unCStr("start-battle"));}),_1zT=[1,_lA,_1zS],_1zU=new T(function(){return B(unCStr("add-tactic-btn"));}),_1zV=[1,_lA,_1zU],_1zW=new T(function(){return B(unCStr("make-party"));}),_1zX=[1,_lA,_1zW],_1zY=[1,_1yR,_P8],_1zZ=new T(function(){return B(unCStr("active"));}),_1A0=function(_1A1){return E(E(_1A1)[7]);},_1A2=new T(function(){return B(unCStr("maximum"));}),_1A3=new T(function(){return B(_a7(_1A2));}),_1A4=function(_1A5,_1A6){var _1A7=E(_1A6);if(!_1A7[0]){return E(_1A3);}else{var _1A8=new T(function(){return B(_1A0(_1A5));}),_1A9=_1A7[2],_1Aa=_1A7[1];while(1){var _1Ab=E(_1A9);if(!_1Ab[0]){return E(_1Aa);}else{_1A9=_1Ab[2];var _1Ac=B(A(_1A8,[E(_1Aa),_1Ab[1]]));_1Aa=_1Ac;continue;}}}},_1Ad=new T(function(){return B(unCStr("\u30b3\u30de\u30f3\u30c9\u5165\u529b"));}),_1Ae=new T(function(){return [1,_1z0,_1Ae];}),_1Af=[1,_1e0,_1yW],_1Ag=[1,_1e0,_1Af],_1Ah=new T(function(){return B(_NT(_NS,_1Ag));}),_1Ai=new T(function(){return B(_O2(_NR,_1Ah));}),_1Aj=new T(function(){return B(_NK(_1Ag,0));}),_1Ak=[0,_Oa,_1Aj,_1Ai],_1Al=new T(function(){return [1,_1Ak,_1Al];}),_1Am=function(_){var _1An=B(_1un(_)),_1Ao=B(_1y5(_1An,_)),_1Ap=nMV([0,_1zd,_1Ao,_1Ao,_1An,_1yE,_wf,_1z7]),_1Aq=_1Ap,_1Ar=rMV(_1Aq),_1As=_1Aq,_1At=function(_1Au,_){var _1Av=rMV(_1Aq),_1Aw=_1Av,_1Ax=new T(function(){var _1Ay=E(_1Aw),_1Az=_1Ay[1],_1AA=new T(function(){return B(_gB(E(_1Au)[1],_UI,_1Az));});return [0,_1AA,_1Ay[2],_1Ay[3],_1Ay[4],_1Ay[5],_1Ay[6],_1Ay[7]];}),_=wMV(_1Aq,_1Ax),_1AB=E(_w5),_1AC=jsFind(_1AB);if(!_1AC[0]){return new F(function(){return _zd(_1AB);});}else{var _1AD=E(_wj),_1AE=_1AD(E(_1AC[1])),_1AF=_1AD(_1AE),_1AG=E(_1zz)(_1AF,toJSStr(E(_1zZ)));if(!_1AG){return _47;}else{var _1AH=rMV(_1Aq),_1AI=E(_1AH),_1AJ=B(_zg(_1As,_1AI[1],_1AI[2],_1AI[4],_1AI[5],_1AI[6],_1AI[7],_)),_1AK=E(_1AJ),_=wMV(_1Aq,E(_1AK[2]));return _1AK[1];}}},_1AL=B(A(_yE,[_4T,_4d,_r,_wg,_1iu,_1At,_])),_1AM=function(_1AN,_){var _1AO=rMV(_1Aq),_1AP=_1AO,_1AQ=new T(function(){var _1AR=E(_1AP),_1AS=_1AR[1],_1AT=new T(function(){return B(_gB(E(_1AN)[1],_125,_1AS));});return [0,_1AT,_1AR[2],_1AR[3],_1AR[4],_1AR[5],_1AR[6],_1AR[7]];}),_=wMV(_1Aq,_1AQ);return _47;},_1AU=B(A(_yE,[_4T,_4d,_r,_wg,_1iv,_1AM,_])),_1AV=rMV(_1Aq),_1AW=E(_1AV),_1AX=B(_zg(_1As,_1AW[1],_1AW[2],_1AW[4],_1AW[5],_1AW[6],_1AW[7],_)),_=wMV(_1Aq,E(E(_1AX)[2])),_1AY="main",_1AZ=jsFind(_1AY);if(!_1AZ[0]){return new F(function(){return _zd(_1AY);});}else{var _1B0=jsQuerySelectorAll(E(_1AZ[1]),toJSStr(_1zX));if(!_1B0[0]){return E(_n1);}else{var _1B1=_1B0[1];if(!E(_1B0[2])[0]){var _1B2=function(_1B3,_){while(1){var _1B4=(function(_1B5,_){var _1B6=E(_1B5);if(!_1B6[0]){return _47;}else{var _1B7=_1B6[1],_1B8=new T(function(){return B(_1x8(_1B7));},1),_1B9=B(_o3(_1B1,_1B8,_));_1B3=_1B6[2];return null;}})(_1B3,_);if(_1B4!=null){return _1B4;}}},_1Ba=function(_1Bb,_1Bc,_){var _1Bd=new T(function(){return B(_1x8(_1Bb));},1),_1Be=B(_o3(_1B1,_1Bd,_));return new F(function(){return _1B2(_1Bc,_);});},_1Bf=B(_1Ba(_Pb,_1zY,_)),_1Bg=B(_Pd(_1Aq,_)),_1Bh="strategy",_1Bi=jsFind(_1Bh);if(!_1Bi[0]){return new F(function(){return _zd(_1Bh);});}else{var _1Bj=E(_1Bi[1]),_1Bk=jsQuerySelectorAll(_1Bj,toJSStr(_1zV));if(!_1Bk[0]){return E(_n1);}else{if(!E(_1Bk[2])[0]){var _1Bl=function(_1Bm,_){var _1Bn=rMV(_1Aq),_1Bo=E(_1Bn),_1Bp=_1Bo[7],_1Bq=new T(function(){var _1Br=E(_1Bp),_1Bs=_1Br[1],_1Bt=_1Br[4],_1Bu=new T(function(){var _1Bv=new T(function(){return B(_9s(B(_1zp(_1Bs,_1Al))));});return B(_gB(B(_1A4(_5t,B(_1zJ(_1Bt))))+1|0,_1Bv,_1Bt));});return [0,_1Bs,_1Br[2],_1Br[3],_1Bu,_1Br[5]];}),_=wMV(_1Aq,[0,_1Bo[1],_1Bo[2],_1Bo[3],_1Bo[4],_1Bo[5],_1Bo[6],_1Bq]);return new F(function(){return _1gO(_1Bj,_1As,_);});},_1Bw=B(A(_yE,[_4T,_4d,_46,_1Bk[1],_w4,_1Bl,_])),_1Bx=B(_1gO(_1Bj,_1As,_)),_1By="battle",_1Bz=jsFind(_1By);if(!_1Bz[0]){return new F(function(){return _zd(_1By);});}else{var _1BA=E(_1Bz[1]),_1BB=_1BA,_1BC=jsQuerySelectorAll(_1BB,toJSStr(_1zT));if(!_1BC[0]){return E(_n1);}else{var _1BD=_1BC[1];if(!E(_1BC[2])[0]){var _1BE=function(_){var _1BF=rMV(_1Aq),_1BG=E(_1BF),_1BH=E(_1BG[7]),_1BI=B(_iY(_1BH[1],_1BH[2],_1BH[3],_1BH[4],_1BH[5],_)),_=wMV(_1Aq,[0,_1BG[1],_1BG[2],_1BG[3],_1BG[4],_1BG[5],_1BG[6],E(_1BI)[2]]),_1BJ=rMV(_1Aq),_1BK=_1BJ,_1BL=new T(function(){return E(E(_1BK)[7]);}),_1BM=B(_n2(_1BB,_1BL,_)),_1BN=rMV(_1Aq);switch(E(E(E(_1BN)[7])[5])){case 1:return new F(function(){return A(_kq,[_4d,_4S,_1BD,_yo,_xD,_]);});break;case 2:return new F(function(){return A(_kq,[_4d,_4S,_1BD,_yo,_xD,_]);});break;default:return _47;}},_1BO=function(_1BP,_){return new F(function(){return _1BE(_);});},_1BQ=function(_1BR,_){var _1BS=B(A(_kq,[_4d,_4S,_1BD,_yo,_yn,_])),_1BT=B(_p2(_1BA,_1Aq,_)),_1BU=jsQuerySelectorAll(_1BB,toJSStr(_yl));if(!_1BU[0]){return E(_n1);}else{if(!E(_1BU[2])[0]){var _1BV=B(A(_yE,[_4T,_4d,_46,_1BU[1],_w4,_1BO,_]));return _47;}else{return E(_n1);}}},_1BW=B(A(_yE,[_4T,_4d,_46,_1BD,_w4,_1BQ,_])),_1BX=jsQuerySelectorAll(_1BB,toJSStr(_1zR));if(!_1BX[0]){return E(_n1);}else{if(!E(_1BX[2])[0]){var _1BY=rMV(_1Aq),_1BZ=_1BY,_1C0=new T(function(){var _1C1=new T(function(){return B(_9s(B(_1zf(E(E(_1BZ)[7])[1],_1Ae))));});return B(_1fI(_1Ad,_125,_1C1));}),_1C2=B(A(_l3,[_4d,_4S,_1BX[1],_l2,_1C0,_])),_1C3=E(_1bX)(E(_3z));return new F(function(){return _48(_);});}else{return E(_n1);}}}else{return E(_n1);}}}}else{return E(_n1);}}}}else{return E(_n1);}}}},_1C4=function(_){return new F(function(){return _1Am(_);});};
var hasteMain = function() {B(A(_1C4, [0]));};window.onload = hasteMain;