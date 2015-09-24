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

var _0="metaKey",_1="shiftKey",_2="altKey",_3="ctrlKey",_4="keyCode",_5=function(_6,_){var _7=_6[E(_4)],_8=_7,_9=_6[E(_3)],_a=_9,_b=_6[E(_2)],_c=_b,_d=_6[E(_1)],_e=_d,_f=_6[E(_0)],_g=_f;return new T(function(){var _h=Number(_8),_i=jsTrunc(_h);return [0,_i,E(_a),E(_c),E(_e),E(_g)];});},_j=function(_k,_l,_){return new F(function(){return _5(E(_l),_);});},_m="keydown",_n="keyup",_o="keypress",_p=function(_q){switch(E(_q)){case 0:return E(_o);case 1:return E(_n);default:return E(_m);}},_r=[0,_p,_j],_s=function(_t,_){return [1,_t];},_u=function(_v){return E(_v);},_w=[0,_u,_s],_x=function(_y,_z,_){var _A=B(A(_y,[_])),_B=B(A(_z,[_]));return _A;},_C=function(_D,_E,_){var _F=B(A(_D,[_])),_G=_F,_H=B(A(_E,[_])),_I=_H;return new T(function(){return B(A(_G,[_I]));});},_J=function(_K,_L,_){var _M=B(A(_L,[_]));return _K;},_N=function(_O,_P,_){var _Q=B(A(_P,[_])),_R=_Q;return new T(function(){return B(A(_O,[_R]));});},_S=[0,_N,_J],_T=function(_U,_){return _U;},_V=function(_W,_X,_){var _Y=B(A(_W,[_]));return new F(function(){return A(_X,[_]);});},_Z=[0,_S,_T,_C,_V,_x],_10=function(_11,_12,_){var _13=B(A(_11,[_]));return new F(function(){return A(_12,[_13,_]);});},_14=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_15=new T(function(){return B(unCStr("base"));}),_16=new T(function(){return B(unCStr("IOException"));}),_17=[0],_18=new T(function(){var _19=hs_wordToWord64(4053623282),_1a=hs_wordToWord64(3693590983);return [0,_19,_1a,[0,_19,_1a,_15,_14,_16],_17,_17];}),_1b=function(_1c){return E(_18);},_1d=function(_1e){return E(E(_1e)[1]);},_1f=function(_1g,_1h,_1i){var _1j=B(A(_1g,[_])),_1k=B(A(_1h,[_])),_1l=hs_eqWord64(_1j[1],_1k[1]);if(!_1l){return [0];}else{var _1m=hs_eqWord64(_1j[2],_1k[2]);return (!_1m)?[0]:[1,_1i];}},_1n=function(_1o){var _1p=E(_1o);return new F(function(){return _1f(B(_1d(_1p[1])),_1b,_1p[2]);});},_1q=new T(function(){return B(unCStr(": "));}),_1r=new T(function(){return B(unCStr(")"));}),_1s=new T(function(){return B(unCStr(" ("));}),_1t=function(_1u,_1v){var _1w=E(_1u);if(!_1w[0]){return E(_1v);}else{var _1x=_1w[2],_1y=new T(function(){return B(_1t(_1x,_1v));});return [1,_1w[1],_1y];}},_1z=new T(function(){return B(unCStr("interrupted"));}),_1A=new T(function(){return B(unCStr("system error"));}),_1B=new T(function(){return B(unCStr("unsatisified constraints"));}),_1C=new T(function(){return B(unCStr("user error"));}),_1D=new T(function(){return B(unCStr("permission denied"));}),_1E=new T(function(){return B(unCStr("illegal operation"));}),_1F=new T(function(){return B(unCStr("end of file"));}),_1G=new T(function(){return B(unCStr("resource exhausted"));}),_1H=new T(function(){return B(unCStr("resource busy"));}),_1I=new T(function(){return B(unCStr("does not exist"));}),_1J=new T(function(){return B(unCStr("already exists"));}),_1K=new T(function(){return B(unCStr("resource vanished"));}),_1L=new T(function(){return B(unCStr("timeout"));}),_1M=new T(function(){return B(unCStr("unsupported operation"));}),_1N=new T(function(){return B(unCStr("hardware fault"));}),_1O=new T(function(){return B(unCStr("inappropriate type"));}),_1P=new T(function(){return B(unCStr("invalid argument"));}),_1Q=new T(function(){return B(unCStr("failed"));}),_1R=new T(function(){return B(unCStr("protocol error"));}),_1S=function(_1T,_1U){switch(E(_1T)){case 0:return new F(function(){return _1t(_1J,_1U);});break;case 1:return new F(function(){return _1t(_1I,_1U);});break;case 2:return new F(function(){return _1t(_1H,_1U);});break;case 3:return new F(function(){return _1t(_1G,_1U);});break;case 4:return new F(function(){return _1t(_1F,_1U);});break;case 5:return new F(function(){return _1t(_1E,_1U);});break;case 6:return new F(function(){return _1t(_1D,_1U);});break;case 7:return new F(function(){return _1t(_1C,_1U);});break;case 8:return new F(function(){return _1t(_1B,_1U);});break;case 9:return new F(function(){return _1t(_1A,_1U);});break;case 10:return new F(function(){return _1t(_1R,_1U);});break;case 11:return new F(function(){return _1t(_1Q,_1U);});break;case 12:return new F(function(){return _1t(_1P,_1U);});break;case 13:return new F(function(){return _1t(_1O,_1U);});break;case 14:return new F(function(){return _1t(_1N,_1U);});break;case 15:return new F(function(){return _1t(_1M,_1U);});break;case 16:return new F(function(){return _1t(_1L,_1U);});break;case 17:return new F(function(){return _1t(_1K,_1U);});break;default:return new F(function(){return _1t(_1z,_1U);});}},_1V=new T(function(){return B(unCStr("}"));}),_1W=new T(function(){return B(unCStr("{handle: "));}),_1X=function(_1Y,_1Z,_20,_21,_22,_23){var _24=new T(function(){var _25=new T(function(){var _26=new T(function(){var _27=E(_21);if(!_27[0]){return E(_23);}else{var _28=new T(function(){var _29=new T(function(){return B(_1t(_1r,_23));},1);return B(_1t(_27,_29));},1);return B(_1t(_1s,_28));}},1);return B(_1S(_1Z,_26));},1),_2a=E(_20);if(!_2a[0]){return E(_25);}else{var _2b=new T(function(){return B(_1t(_1q,_25));},1);return B(_1t(_2a,_2b));}},1),_2c=E(_22);if(!_2c[0]){var _2d=E(_1Y);if(!_2d[0]){return E(_24);}else{var _2e=E(_2d[1]);if(!_2e[0]){var _2f=_2e[1],_2g=new T(function(){var _2h=new T(function(){var _2i=new T(function(){return B(_1t(_1q,_24));},1);return B(_1t(_1V,_2i));},1);return B(_1t(_2f,_2h));},1);return new F(function(){return _1t(_1W,_2g);});}else{var _2j=_2e[1],_2k=new T(function(){var _2l=new T(function(){var _2m=new T(function(){return B(_1t(_1q,_24));},1);return B(_1t(_1V,_2m));},1);return B(_1t(_2j,_2l));},1);return new F(function(){return _1t(_1W,_2k);});}}}else{var _2n=new T(function(){return B(_1t(_1q,_24));},1);return new F(function(){return _1t(_2c[1],_2n);});}},_2o=function(_2p){var _2q=E(_2p);return new F(function(){return _1X(_2q[1],_2q[2],_2q[3],_2q[4],_2q[6],_17);});},_2r=function(_2s,_2t,_2u){var _2v=E(_2t);return new F(function(){return _1X(_2v[1],_2v[2],_2v[3],_2v[4],_2v[6],_2u);});},_2w=function(_2x,_2y){var _2z=E(_2x);return new F(function(){return _1X(_2z[1],_2z[2],_2z[3],_2z[4],_2z[6],_2y);});},_2A=44,_2B=93,_2C=91,_2D=function(_2E,_2F,_2G){var _2H=E(_2F);if(!_2H[0]){return new F(function(){return unAppCStr("[]",_2G);});}else{var _2I=_2H[1],_2J=_2H[2],_2K=new T(function(){var _2L=new T(function(){var _2M=[1,_2B,_2G],_2N=function(_2O){var _2P=E(_2O);if(!_2P[0]){return E(_2M);}else{var _2Q=_2P[1],_2R=_2P[2],_2S=new T(function(){var _2T=new T(function(){return B(_2N(_2R));});return B(A(_2E,[_2Q,_2T]));});return [1,_2A,_2S];}};return B(_2N(_2J));});return B(A(_2E,[_2I,_2L]));});return [1,_2C,_2K];}},_2U=function(_2V,_2W){return new F(function(){return _2D(_2w,_2V,_2W);});},_2X=[0,_2r,_2o,_2U],_2Y=new T(function(){return [0,_1b,_2X,_2Z,_1n,_2o];}),_2Z=function(_30){return [0,_2Y,_30];},_31=[0],_32=7,_33=function(_34){return [0,_31,_32,_17,_34,_31,_31];},_35=function(_36,_){var _37=new T(function(){var _38=new T(function(){return B(_33(_36));});return B(_2Z(_38));});return new F(function(){return die(_37);});},_39=[0,_Z,_10,_V,_T,_35],_3a=[0,_39,_u],_3b=[0,_3a,_T],_3c="deltaZ",_3d="deltaY",_3e="deltaX",_3f=function(_3g,_3h){var _3i=jsShowI(_3g);return new F(function(){return _1t(fromJSStr(_3i),_3h);});},_3j=41,_3k=40,_3l=function(_3m,_3n,_3o){if(_3n>=0){return new F(function(){return _3f(_3n,_3o);});}else{if(_3m<=6){return new F(function(){return _3f(_3n,_3o);});}else{var _3p=new T(function(){var _3q=jsShowI(_3n);return B(_1t(fromJSStr(_3q),[1,_3j,_3o]));});return [1,_3k,_3p];}}},_3r=new T(function(){return B(unCStr(")"));}),_3s=new T(function(){return B(_3l(0,2,_3r));}),_3t=new T(function(){return B(unAppCStr(") is outside of enumeration\'s range (0,",_3s));}),_3u=function(_3v){var _3w=new T(function(){return B(_3l(0,_3v,_3t));});return new F(function(){return err(B(unAppCStr("toEnum{MouseButton}: tag (",_3w)));});},_3x=function(_3y,_){return new T(function(){var _3z=Number(E(_3y)),_3A=jsTrunc(_3z);if(_3A<0){return B(_3u(_3A));}else{if(_3A>2){return B(_3u(_3A));}else{return _3A;}}});},_3B=0,_3C=[0,_3B,_3B,_3B],_3D="button",_3E=new T(function(){return jsGetMouseCoords;}),_3F=function(_3G,_){var _3H=E(_3G);if(!_3H[0]){return _17;}else{var _3I=_3H[1],_3J=B(_3F(_3H[2],_)),_3K=new T(function(){var _3L=Number(E(_3I));return jsTrunc(_3L);});return [1,_3K,_3J];}},_3M=function(_3N,_){var _3O=__arr2lst(0,_3N);return new F(function(){return _3F(_3O,_);});},_3P=function(_3Q,_){return new F(function(){return _3M(E(_3Q),_);});},_3R=function(_3S,_){return new T(function(){var _3T=Number(E(_3S));return jsTrunc(_3T);});},_3U=[0,_3R,_3P],_3V=function(_3W,_){var _3X=E(_3W);if(!_3X[0]){return _17;}else{var _3Y=B(_3V(_3X[2],_));return [1,_3X[1],_3Y];}},_3Z=new T(function(){return B(unCStr("Pattern match failure in do expression at src/Haste/Prim/Any.hs:272:5-9"));}),_40=[0,_31,_32,_17,_3Z,_31,_31],_41=new T(function(){return B(_2Z(_40));}),_42=function(_){return new F(function(){return die(_41);});},_43=function(_44){return E(E(_44)[1]);},_45=function(_46,_47,_48,_){var _49=__arr2lst(0,_48),_4a=B(_3V(_49,_)),_4b=E(_4a);if(!_4b[0]){return new F(function(){return _42(_);});}else{var _4c=E(_4b[2]);if(!_4c[0]){return new F(function(){return _42(_);});}else{if(!E(_4c[2])[0]){var _4d=B(A(_43,[_46,_4b[1],_])),_4e=B(A(_43,[_47,_4c[1],_]));return [0,_4d,_4e];}else{return new F(function(){return _42(_);});}}}},_4f=function(_){return new F(function(){return __jsNull();});},_4g=function(_4h){var _4i=B(A(_4h,[_]));return E(_4i);},_4j=new T(function(){return B(_4g(_4f));}),_4k=new T(function(){return E(_4j);}),_4l=function(_4m,_4n,_){if(E(_4m)==7){var _4o=E(_3E)(_4n),_4p=B(_45(_3U,_3U,_4o,_)),_4q=_4p,_4r=_4n[E(_3e)],_4s=_4r,_4t=_4n[E(_3d)],_4u=_4t,_4v=_4n[E(_3c)],_4w=_4v;return new T(function(){return [0,E(_4q),E(_31),[0,_4s,_4u,_4w]];});}else{var _4x=E(_3E)(_4n),_4y=B(_45(_3U,_3U,_4x,_)),_4z=_4y,_4A=_4n[E(_3D)],_4B=__eq(_4A,E(_4k));if(!E(_4B)){var _4C=B(_3x(_4A,_)),_4D=_4C;return new T(function(){return [0,E(_4z),[1,_4D],E(_3C)];});}else{return new T(function(){return [0,E(_4z),E(_31),E(_3C)];});}}},_4E=function(_4F,_4G,_){return new F(function(){return _4l(_4F,E(_4G),_);});},_4H="mouseout",_4I="mouseover",_4J="mousemove",_4K="mouseup",_4L="mousedown",_4M="dblclick",_4N="click",_4O="wheel",_4P=function(_4Q){switch(E(_4Q)){case 0:return E(_4N);case 1:return E(_4M);case 2:return E(_4L);case 3:return E(_4K);case 4:return E(_4J);case 5:return E(_4I);case 6:return E(_4H);default:return E(_4O);}},_4R=[0,_4P,_4E],_4S=new T(function(){return B(unCStr("}"));}),_4T=new T(function(){return B(unCStr(", "));}),_4U=new T(function(){return B(unCStr("Escape"));}),_4V=new T(function(){return B(unCStr("Defence"));}),_4W=new T(function(){return B(unCStr("Attack"));}),_4X=function(_4Y){switch(E(_4Y)){case 0:return E(_4W);case 1:return E(_4V);default:return E(_4U);}},_4Z=function(_50,_51){switch(E(_50)){case 0:return new F(function(){return _1t(_4W,_51);});break;case 1:return new F(function(){return _1t(_4V,_51);});break;default:return new F(function(){return _1t(_4U,_51);});}},_52=function(_53,_54){return new F(function(){return _2D(_4Z,_53,_54);});},_55=function(_56,_57,_58){return new F(function(){return _4Z(_57,_58);});},_59=[0,_55,_4X,_52],_5a=new T(function(){return B(unCStr("commandMap = "));}),_5b=new T(function(){return B(unCStr("listSize = "));}),_5c=new T(function(){return B(unCStr("index = "));}),_5d=new T(function(){return B(unCStr("CommandList {"));}),_5e=function(_5f,_5g,_5h){var _5i=new T(function(){return B(A(_5g,[_5h]));});return new F(function(){return A(_5f,[[1,_2A,_5i]]);});},_5j=new T(function(){return B(unCStr("fromList "));}),_5k=new T(function(){return B(unCStr(": empty list"));}),_5l=new T(function(){return B(unCStr("Prelude."));}),_5m=function(_5n){var _5o=new T(function(){return B(_1t(_5n,_5k));},1);return new F(function(){return err(B(_1t(_5l,_5o)));});},_5p=new T(function(){return B(unCStr("foldr1"));}),_5q=new T(function(){return B(_5m(_5p));}),_5r=function(_5s,_5t){var _5u=E(_5t);if(!_5u[0]){return E(_5q);}else{var _5v=_5u[1],_5w=E(_5u[2]);if(!_5w[0]){return E(_5v);}else{var _5x=new T(function(){return B(_5r(_5s,_5w));});return new F(function(){return A(_5s,[_5v,_5x]);});}}},_5y=0,_5z=function(_5A){return E(E(_5A)[1]);},_5B=function(_5C,_5D){while(1){var _5E=(function(_5F,_5G){var _5H=E(_5G);switch(_5H[0]){case 0:var _5I=_5H[4],_5J=new T(function(){return B(_5B(_5F,_5I));});_5C=_5J;_5D=_5H[3];return null;case 1:return [1,[0,_5H[1],_5H[2]],_5F];default:return E(_5F);}})(_5C,_5D);if(_5E!=null){return _5E;}}},_5K=function(_5L){var _5M=E(_5L);if(!_5M[0]){var _5N=_5M[3],_5O=_5M[4];if(_5M[2]>=0){var _5P=new T(function(){return B(_5B(_17,_5O));});return new F(function(){return _5B(_5P,_5N);});}else{var _5Q=new T(function(){return B(_5B(_17,_5N));});return new F(function(){return _5B(_5Q,_5O);});}}else{return new F(function(){return _5B(_17,_5M);});}},_5R=function(_5S,_5T,_5U){var _5V=new T(function(){return B(_5K(_5U));}),_5W=function(_5X,_5Y){var _5Z=E(_5X),_60=_5Z[1],_61=_5Z[2],_62=new T(function(){var _63=new T(function(){return B(A(_5z,[_5S,_5y,_61]));}),_64=function(_65){return new F(function(){return _3l(0,E(_60),_65);});};return B(A(_5r,[_5e,[1,_64,[1,_63,_17]],[1,_3j,_5Y]]));});return [1,_3k,_62];};if(_5T<=10){var _66=function(_67){var _68=new T(function(){return B(_2D(_5W,_5V,_67));},1);return new F(function(){return _1t(_5j,_68);});};return E(_66);}else{var _69=function(_6a){var _6b=new T(function(){var _6c=new T(function(){return B(_2D(_5W,_5V,[1,_3j,_6a]));},1);return B(_1t(_5j,_6c));});return [1,_3k,_6b];};return E(_69);}},_6d=function(_6e,_6f,_6g,_6h){var _6i=new T(function(){return B(_5R(_59,0,_6h));}),_6j=function(_6k){var _6l=new T(function(){var _6m=new T(function(){var _6n=new T(function(){var _6o=new T(function(){var _6p=new T(function(){var _6q=new T(function(){var _6r=new T(function(){var _6s=new T(function(){var _6t=new T(function(){return B(_1t(_4S,_6k));});return B(A(_6i,[_6t]));},1);return B(_1t(_5a,_6s));},1);return B(_1t(_4T,_6r));});return B(_3l(0,E(_6g),_6q));},1);return B(_1t(_5b,_6p));},1);return B(_1t(_4T,_6o));});return B(_3l(0,E(_6f),_6n));},1);return B(_1t(_5c,_6m));},1);return new F(function(){return _1t(_5d,_6l);});};if(_6e<11){return E(_6j);}else{var _6u=function(_6v){var _6w=new T(function(){return B(_6j([1,_3j,_6v]));});return [1,_3k,_6w];};return E(_6u);}},_6x=new T(function(){return B(unCStr("_commandList = "));}),_6y=new T(function(){return B(unCStr("_mp = "));}),_6z=new T(function(){return B(unCStr("_intelligence = "));}),_6A=new T(function(){return B(unCStr("_strength = "));}),_6B=new T(function(){return B(unCStr("_name = "));}),_6C=new T(function(){return B(unCStr("Character {"));}),_6D=new T(function(){return B(unCStr("_maxMP = "));}),_6E=new T(function(){return B(unCStr("_hp = "));}),_6F=new T(function(){return B(unCStr("_maxHP = "));}),_6G=new T(function(){return B(unCStr("_level = "));}),_6H=new T(function(){return B(unCStr("_luck = "));}),_6I=new T(function(){return B(unCStr("_agility = "));}),_6J=new T(function(){return B(unCStr("_vitality = "));}),_6K=new T(function(){return B(unCStr("_technique = "));}),_6L=new T(function(){return B(unCStr("!!: negative index"));}),_6M=new T(function(){return B(_1t(_5l,_6L));}),_6N=new T(function(){return B(err(_6M));}),_6O=new T(function(){return B(unCStr("!!: index too large"));}),_6P=new T(function(){return B(_1t(_5l,_6O));}),_6Q=new T(function(){return B(err(_6P));}),_6R=function(_6S,_6T){while(1){var _6U=E(_6S);if(!_6U[0]){return E(_6Q);}else{var _6V=E(_6T);if(!_6V){return E(_6U[1]);}else{_6S=_6U[2];_6T=_6V-1|0;continue;}}}},_6W=function(_6X,_6Y){if(_6Y>=0){return new F(function(){return _6R(_6X,_6Y);});}else{return E(_6N);}},_6Z=new T(function(){return B(unCStr("ACK"));}),_70=new T(function(){return B(unCStr("BEL"));}),_71=new T(function(){return B(unCStr("BS"));}),_72=new T(function(){return B(unCStr("SP"));}),_73=[1,_72,_17],_74=new T(function(){return B(unCStr("US"));}),_75=[1,_74,_73],_76=new T(function(){return B(unCStr("RS"));}),_77=[1,_76,_75],_78=new T(function(){return B(unCStr("GS"));}),_79=[1,_78,_77],_7a=new T(function(){return B(unCStr("FS"));}),_7b=[1,_7a,_79],_7c=new T(function(){return B(unCStr("ESC"));}),_7d=[1,_7c,_7b],_7e=new T(function(){return B(unCStr("SUB"));}),_7f=[1,_7e,_7d],_7g=new T(function(){return B(unCStr("EM"));}),_7h=[1,_7g,_7f],_7i=new T(function(){return B(unCStr("CAN"));}),_7j=[1,_7i,_7h],_7k=new T(function(){return B(unCStr("ETB"));}),_7l=[1,_7k,_7j],_7m=new T(function(){return B(unCStr("SYN"));}),_7n=[1,_7m,_7l],_7o=new T(function(){return B(unCStr("NAK"));}),_7p=[1,_7o,_7n],_7q=new T(function(){return B(unCStr("DC4"));}),_7r=[1,_7q,_7p],_7s=new T(function(){return B(unCStr("DC3"));}),_7t=[1,_7s,_7r],_7u=new T(function(){return B(unCStr("DC2"));}),_7v=[1,_7u,_7t],_7w=new T(function(){return B(unCStr("DC1"));}),_7x=[1,_7w,_7v],_7y=new T(function(){return B(unCStr("DLE"));}),_7z=[1,_7y,_7x],_7A=new T(function(){return B(unCStr("SI"));}),_7B=[1,_7A,_7z],_7C=new T(function(){return B(unCStr("SO"));}),_7D=[1,_7C,_7B],_7E=new T(function(){return B(unCStr("CR"));}),_7F=[1,_7E,_7D],_7G=new T(function(){return B(unCStr("FF"));}),_7H=[1,_7G,_7F],_7I=new T(function(){return B(unCStr("VT"));}),_7J=[1,_7I,_7H],_7K=new T(function(){return B(unCStr("LF"));}),_7L=[1,_7K,_7J],_7M=new T(function(){return B(unCStr("HT"));}),_7N=[1,_7M,_7L],_7O=[1,_71,_7N],_7P=[1,_70,_7O],_7Q=[1,_6Z,_7P],_7R=new T(function(){return B(unCStr("ENQ"));}),_7S=[1,_7R,_7Q],_7T=new T(function(){return B(unCStr("EOT"));}),_7U=[1,_7T,_7S],_7V=new T(function(){return B(unCStr("ETX"));}),_7W=[1,_7V,_7U],_7X=new T(function(){return B(unCStr("STX"));}),_7Y=[1,_7X,_7W],_7Z=new T(function(){return B(unCStr("SOH"));}),_80=[1,_7Z,_7Y],_81=new T(function(){return B(unCStr("NUL"));}),_82=[1,_81,_80],_83=92,_84=new T(function(){return B(unCStr("\\DEL"));}),_85=new T(function(){return B(unCStr("\\a"));}),_86=new T(function(){return B(unCStr("\\\\"));}),_87=new T(function(){return B(unCStr("\\SO"));}),_88=new T(function(){return B(unCStr("\\r"));}),_89=new T(function(){return B(unCStr("\\f"));}),_8a=new T(function(){return B(unCStr("\\v"));}),_8b=new T(function(){return B(unCStr("\\n"));}),_8c=new T(function(){return B(unCStr("\\t"));}),_8d=new T(function(){return B(unCStr("\\b"));}),_8e=function(_8f,_8g){if(_8f<=127){var _8h=E(_8f);switch(_8h){case 92:return new F(function(){return _1t(_86,_8g);});break;case 127:return new F(function(){return _1t(_84,_8g);});break;default:if(_8h<32){var _8i=E(_8h);switch(_8i){case 7:return new F(function(){return _1t(_85,_8g);});break;case 8:return new F(function(){return _1t(_8d,_8g);});break;case 9:return new F(function(){return _1t(_8c,_8g);});break;case 10:return new F(function(){return _1t(_8b,_8g);});break;case 11:return new F(function(){return _1t(_8a,_8g);});break;case 12:return new F(function(){return _1t(_89,_8g);});break;case 13:return new F(function(){return _1t(_88,_8g);});break;case 14:var _8j=new T(function(){var _8k=E(_8g);if(!_8k[0]){return [0];}else{if(E(_8k[1])==72){return B(unAppCStr("\\&",_8k));}else{return E(_8k);}}},1);return new F(function(){return _1t(_87,_8j);});break;default:var _8l=new T(function(){return B(_6W(_82,_8i));});return new F(function(){return _1t([1,_83,_8l],_8g);});}}else{return [1,_8h,_8g];}}}else{var _8m=new T(function(){var _8n=jsShowI(_8f),_8o=new T(function(){var _8p=E(_8g);if(!_8p[0]){return [0];}else{var _8q=E(_8p[1]);if(_8q<48){return E(_8p);}else{if(_8q>57){return E(_8p);}else{return B(unAppCStr("\\&",_8p));}}}},1);return B(_1t(fromJSStr(_8n),_8o));});return [1,_83,_8m];}},_8r=new T(function(){return B(unCStr("\\\""));}),_8s=function(_8t,_8u){var _8v=E(_8t);if(!_8v[0]){return E(_8u);}else{var _8w=_8v[2],_8x=E(_8v[1]);if(_8x==34){var _8y=new T(function(){return B(_8s(_8w,_8u));},1);return new F(function(){return _1t(_8r,_8y);});}else{var _8z=new T(function(){return B(_8s(_8w,_8u));});return new F(function(){return _8e(_8x,_8z);});}}},_8A=34,_8B=function(_8C,_8D,_8E,_8F,_8G,_8H,_8I,_8J,_8K,_8L,_8M,_8N,_8O,_8P){var _8Q=new T(function(){var _8R=E(_8P);return B(_6d(0,_8R[1],_8R[2],_8R[3]));}),_8S=function(_8T){var _8U=new T(function(){var _8V=new T(function(){var _8W=new T(function(){var _8X=new T(function(){var _8Y=new T(function(){var _8Z=new T(function(){var _90=new T(function(){var _91=new T(function(){var _92=new T(function(){var _93=new T(function(){var _94=new T(function(){var _95=new T(function(){var _96=new T(function(){var _97=new T(function(){var _98=new T(function(){var _99=new T(function(){var _9a=new T(function(){var _9b=new T(function(){var _9c=new T(function(){var _9d=new T(function(){var _9e=new T(function(){var _9f=new T(function(){var _9g=new T(function(){var _9h=new T(function(){var _9i=new T(function(){var _9j=new T(function(){var _9k=new T(function(){var _9l=new T(function(){var _9m=new T(function(){var _9n=new T(function(){var _9o=new T(function(){var _9p=new T(function(){var _9q=new T(function(){var _9r=new T(function(){var _9s=new T(function(){var _9t=new T(function(){var _9u=new T(function(){var _9v=new T(function(){var _9w=new T(function(){return B(_1t(_4S,_8T));});return B(A(_8Q,[_9w]));},1);return B(_1t(_6x,_9v));},1);return B(_1t(_4T,_9u));});return B(_3l(0,E(_8O),_9t));},1);return B(_1t(_6y,_9s));},1);return B(_1t(_4T,_9r));});return B(_3l(0,E(_8N),_9q));},1);return B(_1t(_6D,_9p));},1);return B(_1t(_4T,_9o));});return B(_3l(0,E(_8M),_9n));},1);return B(_1t(_6E,_9m));},1);return B(_1t(_4T,_9l));});return B(_3l(0,E(_8L),_9k));},1);return B(_1t(_6F,_9j));},1);return B(_1t(_4T,_9i));});return B(_3l(0,E(_8K),_9h));},1);return B(_1t(_6G,_9g));},1);return B(_1t(_4T,_9f));});return B(_3l(0,E(_8J),_9e));},1);return B(_1t(_6H,_9d));},1);return B(_1t(_4T,_9c));});return B(_3l(0,E(_8I),_9b));},1);return B(_1t(_6I,_9a));},1);return B(_1t(_4T,_99));});return B(_3l(0,E(_8H),_98));},1);return B(_1t(_6J,_97));},1);return B(_1t(_4T,_96));});return B(_3l(0,E(_8G),_95));},1);return B(_1t(_6K,_94));},1);return B(_1t(_4T,_93));});return B(_3l(0,E(_8F),_92));},1);return B(_1t(_6z,_91));},1);return B(_1t(_4T,_90));});return B(_3l(0,E(_8E),_8Z));},1);return B(_1t(_6A,_8Y));},1);return B(_1t(_4T,_8X));});return B(_8s(_8D,[1,_8A,_8W]));});return B(_1t(_6B,[1,_8A,_8V]));},1);return new F(function(){return _1t(_6C,_8U);});};if(_8C<11){return E(_8S);}else{var _9x=function(_9y){var _9z=new T(function(){return B(_8S([1,_3j,_9y]));});return [1,_3k,_9z];};return E(_9x);}},_9A=function(_9B){var _9C=E(_9B);return new F(function(){return _8B(0,_9C[1],_9C[2],_9C[3],_9C[4],_9C[5],_9C[6],_9C[7],_9C[8],_9C[9],_9C[10],_9C[11],_9C[12],_9C[13]);});},_9D=function(_9E){var _9F=E(_9E);if(!_9F[0]){return [0,_17,_17];}else{var _9G=_9F[2],_9H=E(_9F[1]),_9I=new T(function(){var _9J=B(_9D(_9G));return [0,_9J[1],_9J[2]];}),_9K=new T(function(){return E(E(_9I)[2]);}),_9L=new T(function(){return E(E(_9I)[1]);});return [0,[1,_9H[1],_9L],[1,_9H[2],_9K]];}},_9M=function(_9N){var _9O=E(_9N);if(!_9O[0]){return [0,_17,_17];}else{var _9P=_9O[2],_9Q=E(_9O[1]),_9R=new T(function(){var _9S=B(_9M(_9P));return [0,_9S[1],_9S[2]];}),_9T=new T(function(){return E(E(_9R)[2]);}),_9U=new T(function(){return E(E(_9R)[1]);});return [0,[1,_9Q[1],_9U],[1,_9Q[2],_9T]];}},_9V=new T(function(){return B(unCStr("\n"));}),_9W=0,_9X=function(_9Y,_9Z,_){var _a0=jsWriteHandle(E(_9Y),toJSStr(E(_9Z)));return _9W;},_a1=function(_a2,_a3,_){var _a4=E(_a2),_a5=jsWriteHandle(_a4,toJSStr(E(_a3)));return new F(function(){return _9X(_a4,_9V,_);});},_a6=function(_a7,_a8){return (_a7>=_a8)?(_a7!=_a8)?2:1:0;},_a9=function(_aa,_ab){return new F(function(){return _a6(E(E(E(_aa)[2])[6]),E(E(E(_ab)[2])[6]));});},_ac=1,_ad=[0,_ac],_ae=new T(function(){return B(unCStr(" is not an element of the map"));}),_af=function(_ag){var _ah=new T(function(){return B(_1t(B(_3l(0,_ag,_17)),_ae));});return new F(function(){return err(B(unAppCStr("IntMap.!: key ",_ah)));});},_ai=function(_aj,_ak){var _al=_aj;while(1){var _am=E(_al);switch(_am[0]){case 0:var _an=_am[2]>>>0;if(((_ak>>>0&((_an-1>>>0^4294967295)>>>0^_an)>>>0)>>>0&4294967295)==_am[1]){if(!((_ak>>>0&_an)>>>0)){_al=_am[3];continue;}else{_al=_am[4];continue;}}else{return new F(function(){return _af(_ak);});}break;case 1:if(_ak!=_am[1]){return new F(function(){return _af(_ak);});}else{return E(_am[2]);}break;default:return new F(function(){return _af(_ak);});}}},_ao=0,_ap=function(_aq,_){var _ar=E(_aq);if(!_ar[0]){return _17;}else{var _as=_ar[1],_at=B(_ap(_ar[2],_)),_au=new T(function(){return E(E(_as)[13]);}),_av=new T(function(){var _aw=E(_as),_ax=new T(function(){var _ay=E(_au),_az=_ay[1],_aA=_ay[2],_aB=new T(function(){var _aC=E(_az);if(_aC!=(E(_aA)-1|0)){return _aC+1|0;}else{return E(_ao);}});return [0,_aB,_aA,_ay[3]];});return [0,_aw[1],_aw[2],_aw[3],_aw[4],_aw[5],_aw[6],_aw[7],_aw[8],_aw[9],_aw[10],_aw[11],_aw[12],_ax];}),_aD=new T(function(){var _aE=E(_au);return B(_ai(_aE[3],E(_aE[1])));});return [1,[0,_aD,_av],_at];}},_aF=function(_aG,_){var _aH=E(_aG);if(!_aH[0]){return _17;}else{var _aI=_aH[1],_aJ=B(_aF(_aH[2],_)),_aK=new T(function(){return E(E(_aI)[13]);}),_aL=new T(function(){var _aM=E(_aI),_aN=new T(function(){var _aO=E(_aK),_aP=_aO[1],_aQ=_aO[2],_aR=new T(function(){var _aS=E(_aP);if(_aS!=(E(_aQ)-1|0)){return _aS+1|0;}else{return E(_ao);}});return [0,_aR,_aQ,_aO[3]];});return [0,_aM[1],_aM[2],_aM[3],_aM[4],_aM[5],_aM[6],_aM[7],_aM[8],_aM[9],_aM[10],_aM[11],_aM[12],_aN];}),_aT=new T(function(){var _aU=E(_aK);return B(_ai(_aU[3],E(_aU[1])));});return [1,[0,_aT,_aL],_aJ];}},_aV=function(_aW,_aX){return E(_aX);},_aY=function(_aZ,_b0){return E(_b0);},_b1=[0,_aY,_aV],_b2=function(_b3,_b4){return E(_b3);},_b5=function(_b6){return E(_b6);},_b7=[0,_b5,_b2],_b8=function(_b9){return E(_b9);},_ba=function(_bb,_bc){while(1){var _bd=E(_bc);if(!_bd[0]){return [0];}else{var _be=_bd[2],_bf=E(_bb);if(_bf==1){return E(_be);}else{_bb=_bf-1|0;_bc=_be;continue;}}}},_bg=function(_bh){return E(E(_bh)[1]);},_bi=function(_bj,_bk,_bl,_bm){var _bn=new T(function(){return E(_bj)-1|0;}),_bo=new T(function(){return 0<E(_bn);}),_bp=new T(function(){var _bq=E(_bj)+1|0;if(_bq>0){return B(_ba(_bq,_bm));}else{return E(_bm);}}),_br=new T(function(){var _bs=new T(function(){return B(_6W(_bm,E(_bj)));});return B(A(_bl,[_bs]));}),_bt=function(_bu){var _bv=[1,_bu,_bp];if(!E(_bo)){return E(_bv);}else{var _bw=function(_bx,_by){var _bz=E(_bx);if(!_bz[0]){return E(_bv);}else{var _bA=_bz[1],_bB=_bz[2],_bC=E(_by);if(_bC==1){return [1,_bA,_bv];}else{var _bD=new T(function(){return B(_bw(_bB,_bC-1|0));});return [1,_bA,_bD];}}};return new F(function(){return _bw(_bm,E(_bn));});}};return new F(function(){return A(_bg,[_bk,_bt,_br]);});},_bE=function(_bF,_bG,_bH,_bI,_){while(1){var _bJ=(function(_bK,_bL,_bM,_bN,_){var _bO=E(_bK);if(!_bO[0]){return [0,_9W,[0,_bL,_bM,_bN]];}else{var _bP=_bO[2],_bQ=E(_bO[1]),_bR=_bQ[2],_bS=E(_bQ[1]);if(!_bS[0]){if(!E(_bS[1])){var _bT=new T(function(){var _bU=function(_bV){var _bW=E(_bV),_bX=_bW[10],_bY=new T(function(){return E(_bX)-((imul(E(E(_bR)[2]),5)|0)-(imul(E(B(_bi(_ao,_b1,_b8,_bL))[5]),2)|0)|0)|0;});return [0,_bW[1],_bW[2],_bW[3],_bW[4],_bW[5],_bW[6],_bW[7],_bW[8],_bW[9],_bY,_bW[11],_bW[12],_bW[13]];};return B(_bi(_ao,_b7,_bU,_bL));});_bF=_bP;_bG=_bT;var _bZ=_bM,_c0=_bN;_bH=_bZ;_bI=_c0;return null;}else{var _c1=new T(function(){var _c2=function(_c3){var _c4=E(_c3),_c5=_c4[10],_c6=new T(function(){return E(_c5)-((imul(E(E(_bR)[2]),5)|0)-(imul(E(B(_bi(_ao,_b1,_b8,_bM))[5]),2)|0)|0)|0;});return [0,_c4[1],_c4[2],_c4[3],_c4[4],_c4[5],_c4[6],_c4[7],_c4[8],_c4[9],_c6,_c4[11],_c4[12],_c4[13]];};return B(_bi(_ao,_b7,_c2,_bM));});_bF=_bP;var _c7=_bL;_bH=_c1;var _c0=_bN;_bG=_c7;_bI=_c0;return null;}}else{_bF=_bP;var _c7=_bL,_bZ=_bM,_c0=_bN;_bG=_c7;_bH=_bZ;_bI=_c0;return null;}}})(_bF,_bG,_bH,_bI,_);if(_bJ!=null){return _bJ;}}},_c8=0,_c9=[0,_c8],_ca=function(_cb,_cc){var _cd=E(_cb);if(!_cd[0]){return [0];}else{var _ce=_cd[1],_cf=_cd[2],_cg=E(_cc);if(!_cg[0]){return [0];}else{var _ch=_cg[2],_ci=new T(function(){return B(_ca(_cf,_ch));}),_cj=new T(function(){var _ck=E(_ce);if(!_ck){return E(_c9);}else{return [1,_ck];}});return [1,[0,_cj,_cg[1]],_ci];}}},_cl=[1,_17,_17],_cm=function(_cn,_co){var _cp=function(_cq,_cr){var _cs=E(_cq);if(!_cs[0]){return E(_cr);}else{var _ct=_cs[1],_cu=_cs[2],_cv=E(_cr);if(!_cv[0]){return E(_cs);}else{var _cw=_cv[1],_cx=_cv[2];if(B(A(_cn,[_ct,_cw]))==2){var _cy=new T(function(){return B(_cp(_cs,_cx));});return [1,_cw,_cy];}else{var _cz=new T(function(){return B(_cp(_cu,_cv));});return [1,_ct,_cz];}}}},_cA=function(_cB){var _cC=E(_cB);if(!_cC[0]){return [0];}else{var _cD=_cC[1],_cE=E(_cC[2]);if(!_cE[0]){return E(_cC);}else{var _cF=_cE[1],_cG=_cE[2],_cH=new T(function(){return B(_cA(_cG));}),_cI=new T(function(){return B(_cp(_cD,_cF));});return [1,_cI,_cH];}}},_cJ=new T(function(){return B(_cK(B(_cA(_17))));}),_cK=function(_cL){while(1){var _cM=E(_cL);if(!_cM[0]){return E(_cJ);}else{if(!E(_cM[2])[0]){return E(_cM[1]);}else{_cL=B(_cA(_cM));continue;}}}},_cN=new T(function(){return B(_cO(_17));}),_cP=function(_cQ,_cR,_cS){while(1){var _cT=(function(_cU,_cV,_cW){var _cX=E(_cW);if(!_cX[0]){return [1,[1,_cU,_cV],_cN];}else{var _cY=_cX[1];if(B(A(_cn,[_cU,_cY]))==2){_cQ=_cY;var _cZ=[1,_cU,_cV];_cS=_cX[2];_cR=_cZ;return null;}else{var _d0=new T(function(){return B(_cO(_cX));});return [1,[1,_cU,_cV],_d0];}}})(_cQ,_cR,_cS);if(_cT!=null){return _cT;}}},_d1=function(_d2,_d3,_d4){while(1){var _d5=(function(_d6,_d7,_d8){var _d9=E(_d8);if(!_d9[0]){var _da=new T(function(){return B(A(_d7,[[1,_d6,_17]]));});return [1,_da,_cN];}else{var _db=_d9[1],_dc=_d9[2];switch(B(A(_cn,[_d6,_db]))){case 0:var _dd=function(_de){return new F(function(){return A(_d7,[[1,_d6,_de]]);});};_d2=_db;_d3=_dd;_d4=_dc;return null;case 1:var _df=function(_dg){return new F(function(){return A(_d7,[[1,_d6,_dg]]);});};_d2=_db;_d3=_df;_d4=_dc;return null;default:var _dh=new T(function(){return B(_cO(_d9));}),_di=new T(function(){return B(A(_d7,[[1,_d6,_17]]));});return [1,_di,_dh];}}})(_d2,_d3,_d4);if(_d5!=null){return _d5;}}},_cO=function(_dj){var _dk=E(_dj);if(!_dk[0]){return E(_cl);}else{var _dl=_dk[1],_dm=E(_dk[2]);if(!_dm[0]){return [1,_dk,_17];}else{var _dn=_dm[1],_do=_dm[2];if(B(A(_cn,[_dl,_dn]))==2){return new F(function(){return _cP(_dn,[1,_dl,_17],_do);});}else{var _dp=function(_dq){return [1,_dl,_dq];};return new F(function(){return _d1(_dn,_dp,_do);});}}}};return new F(function(){return _cK(B(_cO(_co)));});},_dr=function(_){return new F(function(){return jsMkStdout();});},_ds=new T(function(){return B(_4g(_dr));}),_dt=function(_du,_dv,_dw,_){var _dx=B(_aF(_du,_)),_dy=B(_9M(_dx)),_dz=_dy[1],_dA=_dy[2],_dB=B(_ap(_dv,_)),_dC=B(_9D(_dB))[2],_dD=new T(function(){return B(_ca(_dz,_dC));}),_dE=function(_dF,_dG){var _dH=E(_dF);if(!_dH[0]){return E(_dD);}else{var _dI=_dH[1],_dJ=_dH[2],_dK=E(_dG);if(!_dK[0]){return E(_dD);}else{var _dL=_dK[2],_dM=new T(function(){return B(_dE(_dJ,_dL));}),_dN=new T(function(){var _dO=E(_dI);if(!_dO){return E(_ad);}else{return [1,_dO];}});return [1,[0,_dN,_dK[1]],_dM];}}},_dP=new T(function(){return E(_dw)+1|0;}),_dQ=B(_bE(B(_cm(_a9,B(_dE(_dz,_dA)))),_dA,_dC,_dP,_)),_dR=E(E(_dQ)[2]),_dS=B(_a1(_ds,B(_2D(_9A,_dR[1],_17)),_)),_dT=B(_a1(_ds,B(_2D(_9A,_dR[2],_17)),_));return [0,_dT,_dR];},_dU=function(_dV,_dW){if(_dV<=0){if(_dV>=0){return new F(function(){return quot(_dV,_dW);});}else{if(_dW<=0){return new F(function(){return quot(_dV,_dW);});}else{return quot(_dV+1|0,_dW)-1|0;}}}else{if(_dW>=0){if(_dV>=0){return new F(function(){return quot(_dV,_dW);});}else{if(_dW<=0){return new F(function(){return quot(_dV,_dW);});}else{return quot(_dV+1|0,_dW)-1|0;}}}else{return quot(_dV-1|0,_dW)-1|0;}}},_dX=new T(function(){return B(unCStr("GHC.Exception"));}),_dY=new T(function(){return B(unCStr("base"));}),_dZ=new T(function(){return B(unCStr("ArithException"));}),_e0=new T(function(){var _e1=hs_wordToWord64(4194982440),_e2=hs_wordToWord64(3110813675);return [0,_e1,_e2,[0,_e1,_e2,_dY,_dX,_dZ],_17,_17];}),_e3=function(_e4){return E(_e0);},_e5=function(_e6){var _e7=E(_e6);return new F(function(){return _1f(B(_1d(_e7[1])),_e3,_e7[2]);});},_e8=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_e9=new T(function(){return B(unCStr("denormal"));}),_ea=new T(function(){return B(unCStr("divide by zero"));}),_eb=new T(function(){return B(unCStr("loss of precision"));}),_ec=new T(function(){return B(unCStr("arithmetic underflow"));}),_ed=new T(function(){return B(unCStr("arithmetic overflow"));}),_ee=function(_ef,_eg){switch(E(_ef)){case 0:return new F(function(){return _1t(_ed,_eg);});break;case 1:return new F(function(){return _1t(_ec,_eg);});break;case 2:return new F(function(){return _1t(_eb,_eg);});break;case 3:return new F(function(){return _1t(_ea,_eg);});break;case 4:return new F(function(){return _1t(_e9,_eg);});break;default:return new F(function(){return _1t(_e8,_eg);});}},_eh=function(_ei){return new F(function(){return _ee(_ei,_17);});},_ej=function(_ek,_el,_em){return new F(function(){return _ee(_el,_em);});},_en=function(_eo,_ep){return new F(function(){return _2D(_ee,_eo,_ep);});},_eq=[0,_ej,_eh,_en],_er=new T(function(){return [0,_e3,_eq,_es,_e5,_eh];}),_es=function(_et){return [0,_er,_et];},_eu=3,_ev=new T(function(){return B(_es(_eu));}),_ew=new T(function(){return die(_ev);}),_ex=0,_ey=new T(function(){return B(_es(_ex));}),_ez=new T(function(){return die(_ey);}),_eA=function(_eB,_eC){var _eD=E(_eC);switch(_eD){case -1:var _eE=E(_eB);if(_eE==(-2147483648)){return E(_ez);}else{return new F(function(){return _dU(_eE,-1);});}break;case 0:return E(_ew);default:return new F(function(){return _dU(_eB,_eD);});}},_eF=new T(function(){return B(unCStr("%"));}),_eG=new T(function(){return B(unCStr("width"));}),_eH=function(_eI){return E(E(_eI)[1]);},_eJ=function(_eK){return E(E(_eK)[2]);},_eL=function(_eM,_eN,_eO,_eP,_eQ){var _eR=function(_){var _eS=jsSetStyle(B(A(_eH,[_eM,_eO])),toJSStr(E(_eP)),toJSStr(E(_eQ)));return _9W;};return new F(function(){return A(_eJ,[_eN,_eR]);});},_eT=function(_eU,_eV,_){while(1){var _eW=(function(_eX,_eY,_){var _eZ=E(_eX);if(!_eZ[0]){return _9W;}else{var _f0=E(_eY);if(!_f0[0]){return _9W;}else{var _f1=_f0[1],_f2=new T(function(){var _f3=E(_f1);return B(_1t(B(_3l(0,B(_eA(imul(E(_f3[10]),100)|0,E(_f3[9]))),_17)),_eF));}),_f4=B(A(_eL,[_w,_3a,_eZ[1],_eG,_f2,_]));_eU=_eZ[2];_eV=_f0[2];return null;}}})(_eU,_eV,_);if(_eW!=null){return _eW;}}},_f5=function(_f6,_f7,_){while(1){var _f8=(function(_f9,_fa,_){var _fb=E(_f9);if(!_fb[0]){return _9W;}else{var _fc=_fb[2],_fd=E(_fa);if(!_fd[0]){return _9W;}else{var _fe=_fd[2],_ff=E(_fd[1]),_fg=_ff[12],_fh=E(_ff[11]);if(!_fh){_f6=_fc;_f7=_fe;return null;}else{var _fi=new T(function(){var _fj=E(_fg),_fk=E(_fh);if(_fk==(-1)){var _fl=imul(_fj,100)|0;if(_fl==(-2147483648)){return E(_ez);}else{return B(_1t(B(_3l(0,B(_dU(_fl,-1)),_17)),_eF));}}else{return B(_1t(B(_3l(0,B(_dU(imul(_fj,100)|0,_fk)),_17)),_eF));}}),_fm=B(A(_eL,[_w,_3a,_fb[1],_eG,_fi,_]));_f6=_fc;_f7=_fe;return null;}}}})(_f6,_f7,_);if(_f8!=null){return _f8;}}},_fn=new T(function(){return B(unCStr("innerHTML"));}),_fo=function(_fp,_fq,_fr,_fs,_ft){var _fu=function(_){var _fv=jsSet(B(A(_eH,[_fp,_fr])),toJSStr(E(_fs)),toJSStr(E(_ft)));return _9W;};return new F(function(){return A(_eJ,[_fq,_fu]);});},_fw=function(_fx,_fy,_){while(1){var _fz=(function(_fA,_fB,_){var _fC=E(_fA);if(!_fC[0]){return _9W;}else{var _fD=E(_fB);if(!_fD[0]){return _9W;}else{var _fE=_fD[1],_fF=new T(function(){return E(E(_fE)[1]);}),_fG=B(A(_fo,[_w,_3a,_fC[1],_fn,_fF,_]));_fx=_fC[2];_fy=_fD[2];return null;}}})(_fx,_fy,_);if(_fz!=null){return _fz;}}},_fH=function(_fI,_fJ,_){while(1){var _fK=(function(_fL,_fM,_){var _fN=E(_fL);if(!_fN[0]){return _9W;}else{var _fO=E(_fM);if(!_fO[0]){return _9W;}else{var _fP=_fO[1],_fQ=new T(function(){var _fR=E(_fP);return B(_1t(B(_3l(0,B(_eA(imul(E(_fR[10]),100)|0,E(_fR[9]))),_17)),_eF));}),_fS=B(A(_eL,[_w,_3a,_fN[1],_eG,_fQ,_]));_fI=_fN[2];_fJ=_fO[2];return null;}}})(_fI,_fJ,_);if(_fK!=null){return _fK;}}},_fT=new T(function(){return B(unCStr("#enemy-display-name"));}),_fU=new T(function(){return B(unCStr("#enemy-chara"));}),_fV=new T(function(){return B(unCStr("#player-chara"));}),_fW=new T(function(){return B(unCStr("#enemy-display-hpratio"));}),_fX=new T(function(){return B(unCStr("#player-display-mpratio"));}),_fY=function(_fZ){return new F(function(){return _3l(0,E(E(_fZ)[11]),_17);});},_g0=new T(function(){return B(unCStr("#player-display-maxmp"));}),_g1=function(_g2){return new F(function(){return _3l(0,E(E(_g2)[12]),_17);});},_g3=new T(function(){return B(unCStr("#player-display-mp"));}),_g4=new T(function(){return B(unCStr("#player-display-hpratio"));}),_g5=function(_g6){return new F(function(){return _3l(0,E(E(_g6)[9]),_17);});},_g7=new T(function(){return B(unCStr("#player-display-maxhp"));}),_g8=function(_g9){return new F(function(){return _3l(0,E(E(_g9)[10]),_17);});},_ga=new T(function(){return B(unCStr("#player-display-hp"));}),_gb=function(_gc){return E(E(_gc)[1]);},_gd=new T(function(){return B(unCStr("#player-display-name"));}),_ge=function(_gf,_gg,_){var _gh=jsQuerySelectorAll(_gf,toJSStr(E(_fV))),_gi=new T(function(){return E(E(_gg)[1]);}),_gj=function(_,_gk){var _gl=jsQuerySelectorAll(_gf,toJSStr(E(_fU))),_gm=new T(function(){return E(E(_gg)[2]);});if(!_gl[0]){return _9W;}else{var _gn=E(_gl[1]),_go=E(_fT),_gp=jsQuerySelectorAll(_gn,toJSStr(_go)),_gq=B(_fw(_gp,_gm,_)),_gr=E(_fW),_gs=jsQuerySelectorAll(_gn,toJSStr(_gr)),_gt=B(_fH(_gs,_gm,_)),_gu=_gl[2],_=_;while(1){var _gv=E(_gu);if(!_gv[0]){return _9W;}else{var _gw=E(_gv[1]),_gx=jsQuerySelectorAll(_gw,toJSStr(_go)),_gy=B(_fw(_gx,_gm,_)),_gz=jsQuerySelectorAll(_gw,toJSStr(_gr)),_gA=B(_fH(_gz,_gm,_));_gu=_gv[2];continue;}}}};if(!_gh[0]){return new F(function(){return _gj(_,_9W);});}else{var _gB=_gh[1],_gC=function(_gD,_gE,_){var _gF=jsQuerySelectorAll(E(_gB),toJSStr(E(_gD))),_gG=_gF,_gH=_gi,_=_;while(1){var _gI=(function(_gJ,_gK,_){var _gL=E(_gJ);if(!_gL[0]){return _9W;}else{var _gM=E(_gK);if(!_gM[0]){return _9W;}else{var _gN=_gM[1],_gO=new T(function(){return B(A(_gE,[_gN]));}),_gP=B(A(_fo,[_w,_3a,_gL[1],_fn,_gO,_]));_gG=_gL[2];_gH=_gM[2];return null;}}})(_gG,_gH,_);if(_gI!=null){return _gI;}}},_gQ=B(_gC(_gd,_gb,_)),_gR=B(_gC(_ga,_g8,_)),_gS=B(_gC(_g7,_g5,_)),_gT=E(_gB),_gU=E(_g4),_gV=jsQuerySelectorAll(_gT,toJSStr(_gU)),_gW=B(_eT(_gV,_gi,_)),_gX=B(_gC(_g3,_g1,_)),_gY=B(_gC(_g0,_fY,_)),_gZ=E(_fX),_h0=jsQuerySelectorAll(_gT,toJSStr(_gZ)),_h1=B(_f5(_h0,_gi,_)),_h2=function(_h3,_){while(1){var _h4=(function(_h5,_){var _h6=E(_h5);if(!_h6[0]){return _9W;}else{var _h7=_h6[1],_h8=function(_h9,_ha,_){var _hb=jsQuerySelectorAll(E(_h7),toJSStr(E(_h9))),_hc=_hb,_hd=_gi,_=_;while(1){var _he=(function(_hf,_hg,_){var _hh=E(_hf);if(!_hh[0]){return _9W;}else{var _hi=E(_hg);if(!_hi[0]){return _9W;}else{var _hj=_hi[1],_hk=new T(function(){return B(A(_ha,[_hj]));}),_hl=B(A(_fo,[_w,_3a,_hh[1],_fn,_hk,_]));_hc=_hh[2];_hd=_hi[2];return null;}}})(_hc,_hd,_);if(_he!=null){return _he;}}},_hm=B(_h8(_gd,_gb,_)),_hn=B(_h8(_ga,_g8,_)),_ho=B(_h8(_g7,_g5,_)),_hp=E(_h7),_hq=jsQuerySelectorAll(_hp,toJSStr(_gU)),_hr=B(_eT(_hq,_gi,_)),_hs=B(_h8(_g3,_g1,_)),_ht=B(_h8(_g0,_fY,_)),_hu=jsQuerySelectorAll(_hp,toJSStr(_gZ)),_hv=B(_f5(_hu,_gi,_));_h3=_h6[2];return null;}})(_h3,_);if(_h4!=null){return _h4;}}},_hw=B(_h2(_gh[2],_));return new F(function(){return _gj(_,_hw);});}},_hx=0,_hy=function(_hz){return E(E(_hz)[1]);},_hA=function(_hB){return E(E(_hB)[2]);},_hC=function(_hD){return new F(function(){return fromJSStr(E(_hD));});},_hE=function(_hF,_hG,_hH,_hI){var _hJ=function(_){return new F(function(){return jsGet(B(A(_eH,[_hF,_hH])),E(_hI));});};return new F(function(){return A(_eJ,[_hG,_hJ]);});},_hK=function(_hL){return E(E(_hL)[4]);},_hM=function(_hN,_hO,_hP,_hQ){var _hR=B(_hy(_hO)),_hS=new T(function(){return B(_hK(_hR));}),_hT=function(_hU){var _hV=new T(function(){return B(_hC(_hU));});return new F(function(){return A(_hS,[_hV]);});},_hW=new T(function(){var _hX=new T(function(){return toJSStr(E(_hQ));});return B(_hE(_hN,_hO,_hP,_hX));});return new F(function(){return A(_hA,[_hR,_hW,_hT]);});},_hY=function(_hZ,_i0,_){var _i1=B(A(_hM,[_w,_3a,_hZ,_fn,_])),_i2=_i1,_i3=new T(function(){return B(_1t(_i2,_i0));});return new F(function(){return A(_fo,[_w,_3a,_hZ,_fn,_i3,_]);});},_i4=new T(function(){return B(unCStr("  <div class=\"enemy\">"));}),_i5=new T(function(){return B(unCStr("    <span id=\"enemy-display-name\"></span><br>"));}),_i6=new T(function(){return B(unCStr("    HP"));}),_i7=new T(function(){return B(unCStr("    <div class=\"progress\">"));}),_i8=new T(function(){return B(unCStr("      <div class=\"progress-bar\" role=\"progressbar\" id=\"enemy-display-hpratio\">"));}),_i9=new T(function(){return B(unCStr("      </div>"));}),_ia=new T(function(){return B(unCStr("    </div>"));}),_ib=new T(function(){return B(unCStr("</div>"));}),_ic=[1,_ib,_17],_id=new T(function(){return B(unCStr("  </div>"));}),_ie=[1,_id,_ic],_if=[1,_ia,_ie],_ig=[1,_i9,_if],_ih=[1,_i8,_ig],_ii=[1,_i7,_ih],_ij=[1,_i6,_ii],_ik=[1,_i5,_ij],_il=[1,_i4,_ik],_im=new T(function(){return B(unCStr("<div class=\"col-md-4\">"));}),_in=function(_io){var _ip=E(_io);if(!_ip[0]){return [0];}else{var _iq=_ip[2],_ir=new T(function(){return B(_in(_iq));},1);return new F(function(){return _1t(_ip[1],_ir);});}},_is=function(_it,_iu){var _iv=new T(function(){return B(_in(_iu));},1);return new F(function(){return _1t(_it,_iv);});},_iw=new T(function(){return B(_is(_im,_il));}),_ix=new T(function(){return B(unCStr("  <div class=\"player\">"));}),_iy=new T(function(){return B(unCStr("    <span id=\"player-display-name\"></span><br>"));}),_iz=new T(function(){return B(unCStr("    HP <span id=\"player-display-hp\"></span> / <span id=\"player-display-maxhp\"></span>"));}),_iA=new T(function(){return B(unCStr("      <div class=\"progress-bar\" role=\"progressbar\" id=\"player-display-hpratio\">"));}),_iB=new T(function(){return B(unCStr("      <div class=\"progress-bar progress-bar-info\" role=\"progressbar\" id=\"player-display-mpratio\">"));}),_iC=[1,_iB,_ig],_iD=[1,_i7,_iC],_iE=new T(function(){return B(unCStr("    MP <span id=\"player-display-mp\"></span> / <span id=\"player-display-maxmp\"></span>"));}),_iF=[1,_iE,_iD],_iG=[1,_ia,_iF],_iH=[1,_i9,_iG],_iI=[1,_iA,_iH],_iJ=[1,_i7,_iI],_iK=[1,_iz,_iJ],_iL=[1,_iy,_iK],_iM=[1,_ix,_iL],_iN=function(_iO){var _iP=E(_iO);if(!_iP[0]){return [0];}else{var _iQ=_iP[2],_iR=new T(function(){return B(_iN(_iQ));},1);return new F(function(){return _1t(_iP[1],_iR);});}},_iS=function(_iT,_iU){var _iV=new T(function(){return B(_iN(_iU));},1);return new F(function(){return _1t(_iT,_iV);});},_iW=new T(function(){return B(_iS(_im,_iM));}),_iX=new T(function(){return B(unCStr("#step-battle"));}),_iY=new T(function(){return B(unCStr("Control.Exception.Base"));}),_iZ=new T(function(){return B(unCStr("base"));}),_j0=new T(function(){return B(unCStr("PatternMatchFail"));}),_j1=new T(function(){var _j2=hs_wordToWord64(18445595),_j3=hs_wordToWord64(52003073);return [0,_j2,_j3,[0,_j2,_j3,_iZ,_iY,_j0],_17,_17];}),_j4=function(_j5){return E(_j1);},_j6=function(_j7){var _j8=E(_j7);return new F(function(){return _1f(B(_1d(_j8[1])),_j4,_j8[2]);});},_j9=function(_ja){return E(E(_ja)[1]);},_jb=function(_jc){return [0,_jd,_jc];},_je=function(_jf,_jg){return new F(function(){return _1t(E(_jf)[1],_jg);});},_jh=function(_ji,_jj){return new F(function(){return _2D(_je,_ji,_jj);});},_jk=function(_jl,_jm,_jn){return new F(function(){return _1t(E(_jm)[1],_jn);});},_jo=[0,_jk,_j9,_jh],_jd=new T(function(){return [0,_j4,_jo,_jb,_j6,_j9];}),_jp=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_jq=function(_jr){return E(E(_jr)[3]);},_js=function(_jt,_ju){var _jv=new T(function(){return B(A(_jq,[_ju,_jt]));});return new F(function(){return die(_jv);});},_jw=function(_jx,_et){return new F(function(){return _js(_jx,_et);});},_jy=function(_jz,_jA){var _jB=E(_jA);if(!_jB[0]){return [0,_17,_17];}else{var _jC=_jB[1],_jD=_jB[2];if(!B(A(_jz,[_jC]))){return [0,_17,_jB];}else{var _jE=new T(function(){var _jF=B(_jy(_jz,_jD));return [0,_jF[1],_jF[2]];}),_jG=new T(function(){return E(E(_jE)[2]);}),_jH=new T(function(){return E(E(_jE)[1]);});return [0,[1,_jC,_jH],_jG];}}},_jI=32,_jJ=new T(function(){return B(unCStr("\n"));}),_jK=function(_jL){return (E(_jL)==124)?false:true;},_jM=function(_jN,_jO){var _jP=B(_jy(_jK,B(unCStr(_jN)))),_jQ=_jP[1],_jR=function(_jS,_jT){var _jU=new T(function(){var _jV=new T(function(){var _jW=new T(function(){return B(_1t(_jT,_jJ));},1);return B(_1t(_jO,_jW));});return B(unAppCStr(": ",_jV));},1);return new F(function(){return _1t(_jS,_jU);});},_jX=E(_jP[2]);if(!_jX[0]){return new F(function(){return _jR(_jQ,_17);});}else{if(E(_jX[1])==124){return new F(function(){return _jR(_jQ,[1,_jI,_jX[2]]);});}else{return new F(function(){return _jR(_jQ,_17);});}}},_jY=function(_jZ){var _k0=new T(function(){return B(_jM(_jZ,_jp));});return new F(function(){return _jw([0,_k0],_jd);});},_k1=function(_k2){return new F(function(){return _jY("Main.hs:(158,35)-(164,30)|lambda");});},_k3=new T(function(){return B(_k1(_));}),_k4=function(_k5){return new F(function(){return _jY("Main.hs:(152,35)-(154,41)|lambda");});},_k6=new T(function(){return B(_k4(_));}),_k7=function(_k8){return new F(function(){return _jY("Main.hs:(148,36)-(150,42)|lambda");});},_k9=new T(function(){return B(_k7(_));}),_ka=function(_kb){var _kc=new T(function(){return B(unCStr(_kb));});return new F(function(){return err(B(unAppCStr("Oops!  Entered absent arg ",_kc)));});},_kd=new T(function(){return B(_ka("ww_sAI4 Int"));}),_ke=function(_kf){return E(E(_kf)[1]);},_kg=function(_kh){return E(E(_kh)[2]);},_ki=function(_kj){return E(E(_kj)[1]);},_kk=function(_){return new F(function(){return nMV(_31);});},_kl=new T(function(){return B(_4g(_kk));}),_km=(function(e,name,f){e.addEventListener(name,f,false);return [f];}),_kn=function(_ko){return E(E(_ko)[2]);},_kp=function(_kq,_kr,_ks,_kt,_ku,_kv){var _kw=B(_ke(_kq)),_kx=B(_hy(_kw)),_ky=new T(function(){return B(_eJ(_kw));}),_kz=new T(function(){return B(_hK(_kx));}),_kA=new T(function(){return B(A(_eH,[_kr,_kt]));}),_kB=new T(function(){return B(A(_ki,[_ks,_ku]));}),_kC=function(_kD){return new F(function(){return A(_kz,[[0,_kB,_kA,_kD]]);});},_kE=function(_kF){var _kG=new T(function(){var _kH=new T(function(){var _kI=E(_kA),_kJ=E(_kB),_kK=E(_kF),_kL=function(_kM,_){var _kN=B(A(_kK,[_kM,_]));return _4k;},_kO=__createJSFunc(2,E(_kL)),_kP=_kO,_kQ=function(_){return new F(function(){return E(_km)(_kI,_kJ,_kP);});};return E(_kQ);});return B(A(_ky,[_kH]));});return new F(function(){return A(_hA,[_kx,_kG,_kC]);});},_kR=new T(function(){var _kS=new T(function(){return B(_eJ(_kw));}),_kT=function(_kU){var _kV=new T(function(){var _kW=function(_){var _=wMV(E(_kl),[1,_kU]);return new F(function(){return A(_kg,[_ks,_ku,_kU,_]);});};return B(A(_kS,[_kW]));});return new F(function(){return A(_hA,[_kx,_kV,_kv]);});};return B(A(_kn,[_kq,_kT]));});return new F(function(){return A(_hA,[_kx,_kR,_kE]);});},_kX=function(_kY,_kZ,_l0,_){var _l1=rMV(_kZ),_l2=E(_kY),_l3=jsQuerySelectorAll(_l2,toJSStr(E(_fV))),_l4=E(E(_l1)[7]),_l5=_l4[1],_l6=_l4[2];if(!_l3[0]){return E(_k9);}else{var _l7=_l3[1];if(!E(_l3[2])[0]){var _l8=function(_l9,_){while(1){var _la=E(_l9);if(!_la[0]){return _9W;}else{var _lb=B(_hY(_l7,_iW,_));_l9=_la[2];continue;}}},_lc=B(_l8(_l5,_)),_ld=jsQuerySelectorAll(_l2,toJSStr(E(_fU)));if(!_ld[0]){return E(_k6);}else{var _le=_ld[1];if(!E(_ld[2])[0]){var _lf=function(_lg,_){while(1){var _lh=E(_lg);if(!_lh[0]){return _9W;}else{var _li=B(_hY(_le,_iw,_));_lg=_lh[2];continue;}}},_lj=B(_lf(_l6,_)),_lk=B(_ge(_l2,[0,_l5,_l6,_kd],_)),_ll=jsQuerySelectorAll(_l2,toJSStr(E(_iX)));if(!_ll[0]){return E(_k3);}else{if(!E(_ll[2])[0]){var _lm=function(_ln,_){var _lo=rMV(_kZ),_lp=E(_lo),_lq=E(_lp[7]),_lr=B(_dt(_lq[1],_lq[2],_lq[3],_)),_=wMV(_kZ,[0,_lp[1],_lp[2],_lp[3],_lp[4],_lp[5],_lp[6],E(_lr)[2]]),_ls=B(A(_l0,[_])),_lt=rMV(_kZ),_lu=_lt,_lv=new T(function(){return E(E(_lu)[7]);});return new F(function(){return _ge(_l2,_lv,_);});},_lw=B(A(_kp,[_3b,_w,_4R,_ll[1],_hx,_lm,_]));return _9W;}else{return E(_k3);}}}else{return E(_k6);}}}else{return E(_k9);}}},_lx=function(_ly,_lz,_lA,_lB){return (_ly!=_lA)?true:(E(_lz)!=E(_lB))?true:false;},_lC=function(_lD,_lE){var _lF=E(_lD),_lG=E(_lE);return new F(function(){return _lx(E(_lF[1]),_lF[2],E(_lG[1]),_lG[2]);});},_lH=function(_lI,_lJ){return E(_lI)==E(_lJ);},_lK=function(_lL,_lM,_lN,_lO){if(_lL!=_lN){return false;}else{return new F(function(){return _lH(_lM,_lO);});}},_lP=function(_lQ,_lR){var _lS=E(_lQ),_lT=E(_lR);return new F(function(){return _lK(E(_lS[1]),_lS[2],E(_lT[1]),_lT[2]);});},_lU=[0,_lP,_lC],_lV=function(_lW,_lX){return new F(function(){return _a6(E(_lW),E(_lX));});},_lY=function(_lZ,_m0,_m1,_m2){if(_lZ>=_m1){if(_lZ!=_m1){return 2;}else{return new F(function(){return _lV(_m0,_m2);});}}else{return 0;}},_m3=function(_m4,_m5){var _m6=E(_m4),_m7=E(_m5);return new F(function(){return _lY(E(_m6[1]),_m6[2],E(_m7[1]),_m7[2]);});},_m8=function(_m9,_ma){return E(_m9)<E(_ma);},_mb=function(_mc,_md,_me,_mf){if(_mc>=_me){if(_mc!=_me){return false;}else{return new F(function(){return _m8(_md,_mf);});}}else{return true;}},_mg=function(_mh,_mi){var _mj=E(_mh),_mk=E(_mi);return new F(function(){return _mb(E(_mj[1]),_mj[2],E(_mk[1]),_mk[2]);});},_ml=function(_mm,_mn){return E(_mm)<=E(_mn);},_mo=function(_mp,_mq,_mr,_ms){if(_mp>=_mr){if(_mp!=_mr){return false;}else{return new F(function(){return _ml(_mq,_ms);});}}else{return true;}},_mt=function(_mu,_mv){var _mw=E(_mu),_mx=E(_mv);return new F(function(){return _mo(E(_mw[1]),_mw[2],E(_mx[1]),_mx[2]);});},_my=function(_mz,_mA){return E(_mz)>E(_mA);},_mB=function(_mC,_mD,_mE,_mF){if(_mC>=_mE){if(_mC!=_mE){return true;}else{return new F(function(){return _my(_mD,_mF);});}}else{return false;}},_mG=function(_mH,_mI){var _mJ=E(_mH),_mK=E(_mI);return new F(function(){return _mB(E(_mJ[1]),_mJ[2],E(_mK[1]),_mK[2]);});},_mL=function(_mM,_mN){return E(_mM)>=E(_mN);},_mO=function(_mP,_mQ,_mR,_mS){if(_mP>=_mR){if(_mP!=_mR){return true;}else{return new F(function(){return _mL(_mQ,_mS);});}}else{return false;}},_mT=function(_mU,_mV){var _mW=E(_mU),_mX=E(_mV);return new F(function(){return _mO(E(_mW[1]),_mW[2],E(_mX[1]),_mX[2]);});},_mY=function(_mZ,_n0){var _n1=E(_mZ),_n2=E(_n1[1]),_n3=E(_n0),_n4=E(_n3[1]);return (_n2>=_n4)?(_n2!=_n4)?E(_n1):(E(_n1[2])>E(_n3[2]))?E(_n1):E(_n3):E(_n3);},_n5=function(_n6,_n7){var _n8=E(_n6),_n9=E(_n8[1]),_na=E(_n7),_nb=E(_na[1]);return (_n9>=_nb)?(_n9!=_nb)?E(_na):(E(_n8[2])>E(_na[2]))?E(_na):E(_n8):E(_n8);},_nc=[0,_lU,_m3,_mg,_mt,_mG,_mT,_mY,_n5],_nd=new T(function(){return B(unCStr("Map.!: given key is not an element in the map"));}),_ne=new T(function(){return B(err(_nd));}),_nf=function(_ng,_nh,_ni){while(1){var _nj=E(_ni);if(!_nj[0]){var _nk=_nj[4],_nl=_nj[5],_nm=E(_nj[2]),_nn=E(_nm[1]);if(_ng>=_nn){if(_ng!=_nn){_ni=_nl;continue;}else{var _no=E(_nm[2]);if(_nh>=_no){if(_nh!=_no){_ni=_nl;continue;}else{return E(_nj[3]);}}else{_ni=_nk;continue;}}}else{_ni=_nk;continue;}}else{return E(_ne);}}},_np=function(_nq,_nr,_ns,_){var _nt=B(A(_nr,[_ns,_])),_nu=_nt,_nv=new T(function(){return E(E(_nu)[2]);});return [0,_nq,_nv];},_nw=function(_nx,_ny,_nz,_){var _nA=B(A(_ny,[_nz,_])),_nB=_nA,_nC=new T(function(){return E(E(_nB)[2]);}),_nD=new T(function(){var _nE=new T(function(){return E(E(_nB)[1]);});return B(A(_nx,[_nE]));});return [0,_nD,_nC];},_nF=[0,_nw,_np],_nG=function(_nH,_nI,_nJ,_){var _nK=B(A(_nH,[_nJ,_])),_nL=_nK,_nM=new T(function(){return E(E(_nL)[2]);}),_nN=B(A(_nI,[_nM,_])),_nO=_nN,_nP=new T(function(){return E(E(_nO)[2]);}),_nQ=new T(function(){var _nR=new T(function(){return E(E(_nO)[1]);});return B(A(E(_nL)[1],[_nR]));});return [0,_nQ,_nP];},_nS=function(_nT,_nU,_nV,_){var _nW=B(A(_nT,[_nV,_])),_nX=_nW,_nY=new T(function(){return E(E(_nX)[2]);}),_nZ=B(A(_nU,[_nY,_])),_o0=_nZ,_o1=new T(function(){return E(E(_o0)[2]);}),_o2=new T(function(){return E(E(_o0)[1]);});return [0,_o2,_o1];},_o3=function(_o4,_o5,_o6,_){var _o7=B(A(_o4,[_o6,_])),_o8=_o7,_o9=new T(function(){return E(E(_o8)[2]);}),_oa=B(A(_o5,[_o9,_])),_ob=_oa,_oc=new T(function(){return E(E(_ob)[2]);}),_od=new T(function(){return E(E(_o8)[1]);});return [0,_od,_oc];},_oe=function(_of,_og,_){return [0,_of,_og];},_oh=[0,_nF,_oe,_nG,_nS,_o3],_oi=function(_oj,_ok,_){return new F(function(){return _35(_oj,_);});},_ol=function(_om,_on,_oo,_){var _op=B(A(_om,[_oo,_])),_oq=_op,_or=new T(function(){return E(E(_oq)[2]);}),_os=new T(function(){return E(E(_oq)[1]);});return new F(function(){return A(_on,[_os,_or,_]);});},_ot=function(_ou,_ov,_ow,_ox,_oy){var _oz=function(_oA){var _oB=new T(function(){return E(E(_oA)[2]);}),_oC=new T(function(){return E(E(_oA)[1]);});return new F(function(){return A(_ox,[_oC,_oB]);});},_oD=new T(function(){return B(A(_ow,[_oy]));});return new F(function(){return A(_hA,[_ov,_oD,_oz]);});},_oE=function(_oF){return E(E(_oF)[5]);},_oG=function(_oH,_oI,_oJ){var _oK=new T(function(){return B(A(_oE,[_oI,_oJ]));}),_oL=function(_oM){return E(_oK);};return E(_oL);},_oN=function(_oO,_oP){var _oQ=function(_oR){return new F(function(){return _oG(_oO,_oP,_oR);});},_oS=function(_oT,_oU){return new F(function(){return A(_hK,[_oP,[0,_oT,_oU]]);});},_oV=function(_oW,_oR){return new F(function(){return _oX(_oO,_oP,_oW,_oR);});},_oY=function(_oZ,_oW,_oR){return new F(function(){return _ot(_oO,_oP,_oZ,_oW,_oR);});};return [0,_oO,_oY,_oV,_oS,_oQ];},_oX=function(_p0,_p1,_p2,_p3){var _p4=function(_p5){return E(_p3);};return new F(function(){return A(_hA,[B(_oN(_p0,_p1)),_p2,_p4]);});},_p6=function(_p7,_p8){return new F(function(){return _oX(_oh,_39,_p7,_p8);});},_p9=[0,_oh,_ol,_p6,_oe,_oi],_pa=function(_pb,_pc,_){var _pd=B(A(_pb,[_]));return [0,_pd,_pc];},_pe=[0,_p9,_pa],_pf=function(_pg,_ph,_pi,_){while(1){var _pj=(function(_pk,_pl,_pm,_){var _pn=E(_pk);if(!_pn[0]){return [0,_9W,_pm];}else{var _po=E(_pl);if(!_po[0]){return [0,_9W,_pm];}else{var _pp=_po[1],_pq=new T(function(){var _pr=E(_pp);return B(_1t(B(_3l(0,B(_eA(imul(E(_pr[10]),100)|0,E(_pr[9]))),_17)),_eF));}),_ps=B(A(_eL,[_w,_pe,_pn[1],_eG,_pq,_pm,_])),_pt=_ps,_pu=new T(function(){return E(E(_pt)[2]);});_pg=_pn[2];_ph=_po[2];_pi=_pu;return null;}}})(_pg,_ph,_pi,_);if(_pj!=null){return _pj;}}},_pv=function(_pw,_px,_py,_){while(1){var _pz=(function(_pA,_pB,_pC,_){var _pD=E(_pA);if(!_pD[0]){return [0,_9W,_pC];}else{var _pE=_pD[2],_pF=E(_pB);if(!_pF[0]){return [0,_9W,_pC];}else{var _pG=_pF[2],_pH=E(_pF[1]),_pI=_pH[12],_pJ=E(_pH[11]);if(!_pJ){_pw=_pE;_px=_pG;var _pK=_pC;_py=_pK;return null;}else{var _pL=new T(function(){var _pM=E(_pI),_pN=E(_pJ);if(_pN==(-1)){var _pO=imul(_pM,100)|0;if(_pO==(-2147483648)){return E(_ez);}else{return B(_1t(B(_3l(0,B(_dU(_pO,-1)),_17)),_eF));}}else{return B(_1t(B(_3l(0,B(_dU(imul(_pM,100)|0,_pN)),_17)),_eF));}}),_pP=B(A(_eL,[_w,_pe,_pD[1],_eG,_pL,_pC,_])),_pQ=_pP,_pR=new T(function(){return E(E(_pQ)[2]);});_pw=_pE;_px=_pG;_py=_pR;return null;}}}})(_pw,_px,_py,_);if(_pz!=null){return _pz;}}},_pS=function(_pT,_pU,_pV,_){while(1){var _pW=(function(_pX,_pY,_pZ,_){var _q0=E(_pX);if(!_q0[0]){return [0,_9W,_pZ];}else{var _q1=E(_pY);if(!_q1[0]){return [0,_9W,_pZ];}else{var _q2=_q1[1],_q3=new T(function(){return E(E(_q2)[1]);}),_q4=B(A(_fo,[_w,_pe,_q0[1],_fn,_q3,_pZ,_])),_q5=_q4,_q6=new T(function(){return E(E(_q5)[2]);});_pT=_q0[2];_pU=_q1[2];_pV=_q6;return null;}}})(_pT,_pU,_pV,_);if(_pW!=null){return _pW;}}},_q7=function(_q8,_q9,_qa,_){while(1){var _qb=(function(_qc,_qd,_qe,_){var _qf=E(_qc);if(!_qf[0]){return [0,_9W,_qe];}else{var _qg=E(_qd);if(!_qg[0]){return [0,_9W,_qe];}else{var _qh=_qg[1],_qi=new T(function(){var _qj=E(_qh);return B(_1t(B(_3l(0,B(_eA(imul(E(_qj[10]),100)|0,E(_qj[9]))),_17)),_eF));}),_qk=B(A(_eL,[_w,_pe,_qf[1],_eG,_qi,_qe,_])),_ql=_qk,_qm=new T(function(){return E(E(_ql)[2]);});_q8=_qf[2];_q9=_qg[2];_qa=_qm;return null;}}})(_q8,_q9,_qa,_);if(_qb!=null){return _qb;}}},_qn=function(_qo,_qp,_qq,_){var _qr=jsQuerySelectorAll(_qo,toJSStr(E(_fV))),_qs=new T(function(){return E(E(_qp)[1]);});if(!_qr[0]){var _qt=jsQuerySelectorAll(_qo,toJSStr(E(_fU))),_qu=new T(function(){return E(E(_qp)[2]);});if(!_qt[0]){return [0,_9W,_qq];}else{var _qv=E(_qt[1]),_qw=E(_fT),_qx=jsQuerySelectorAll(_qv,toJSStr(_qw)),_qy=B(_pS(_qx,_qu,_qq,_)),_qz=_qy,_qA=E(_fW),_qB=jsQuerySelectorAll(_qv,toJSStr(_qA)),_qC=new T(function(){return E(E(_qz)[2]);}),_qD=B(_q7(_qB,_qu,_qC,_)),_qE=_qD,_qF=function(_qG,_qH,_){while(1){var _qI=(function(_qJ,_qK,_){var _qL=E(_qJ);if(!_qL[0]){return [0,_9W,_qK];}else{var _qM=E(_qL[1]),_qN=jsQuerySelectorAll(_qM,toJSStr(_qw)),_qO=B(_pS(_qN,_qu,_qK,_)),_qP=_qO,_qQ=jsQuerySelectorAll(_qM,toJSStr(_qA)),_qR=new T(function(){return E(E(_qP)[2]);}),_qS=B(_q7(_qQ,_qu,_qR,_)),_qT=_qS,_qU=new T(function(){return E(E(_qT)[2]);});_qG=_qL[2];_qH=_qU;return null;}})(_qG,_qH,_);if(_qI!=null){return _qI;}}},_qV=new T(function(){return E(E(_qE)[2]);});return new F(function(){return _qF(_qt[2],_qV,_);});}}else{var _qW=_qr[1],_qX=function(_qY,_qZ,_r0,_){var _r1=jsQuerySelectorAll(E(_qW),toJSStr(E(_qY))),_r2=_r1,_r3=_qs,_r4=_r0,_=_;while(1){var _r5=(function(_r6,_r7,_r8,_){var _r9=E(_r6);if(!_r9[0]){return [0,_9W,_r8];}else{var _ra=E(_r7);if(!_ra[0]){return [0,_9W,_r8];}else{var _rb=_ra[1],_rc=new T(function(){return B(A(_qZ,[_rb]));}),_rd=B(A(_fo,[_w,_pe,_r9[1],_fn,_rc,_r8,_])),_re=_rd,_rf=new T(function(){return E(E(_re)[2]);});_r2=_r9[2];_r3=_ra[2];_r4=_rf;return null;}}})(_r2,_r3,_r4,_);if(_r5!=null){return _r5;}}},_rg=B(_qX(_gd,_gb,_qq,_)),_rh=_rg,_ri=new T(function(){return E(E(_rh)[2]);}),_rj=B(_qX(_ga,_g8,_ri,_)),_rk=_rj,_rl=new T(function(){return E(E(_rk)[2]);}),_rm=B(_qX(_g7,_g5,_rl,_)),_rn=_rm,_ro=E(_qW),_rp=E(_g4),_rq=jsQuerySelectorAll(_ro,toJSStr(_rp)),_rr=new T(function(){return E(E(_rn)[2]);}),_rs=B(_pf(_rq,_qs,_rr,_)),_rt=_rs,_ru=new T(function(){return E(E(_rt)[2]);}),_rv=B(_qX(_g3,_g1,_ru,_)),_rw=_rv,_rx=new T(function(){return E(E(_rw)[2]);}),_ry=B(_qX(_g0,_fY,_rx,_)),_rz=_ry,_rA=E(_fX),_rB=jsQuerySelectorAll(_ro,toJSStr(_rA)),_rC=new T(function(){return E(E(_rz)[2]);}),_rD=B(_pv(_rB,_qs,_rC,_)),_rE=_rD,_rF=function(_rG,_rH,_){while(1){var _rI=(function(_rJ,_rK,_){var _rL=E(_rJ);if(!_rL[0]){return [0,_9W,_rK];}else{var _rM=_rL[1],_rN=function(_rO,_rP,_rQ,_){var _rR=jsQuerySelectorAll(E(_rM),toJSStr(E(_rO))),_rS=_rR,_rT=_qs,_rU=_rQ,_=_;while(1){var _rV=(function(_rW,_rX,_rY,_){var _rZ=E(_rW);if(!_rZ[0]){return [0,_9W,_rY];}else{var _s0=E(_rX);if(!_s0[0]){return [0,_9W,_rY];}else{var _s1=_s0[1],_s2=new T(function(){return B(A(_rP,[_s1]));}),_s3=B(A(_fo,[_w,_pe,_rZ[1],_fn,_s2,_rY,_])),_s4=_s3,_s5=new T(function(){return E(E(_s4)[2]);});_rS=_rZ[2];_rT=_s0[2];_rU=_s5;return null;}}})(_rS,_rT,_rU,_);if(_rV!=null){return _rV;}}},_s6=B(_rN(_gd,_gb,_rK,_)),_s7=_s6,_s8=new T(function(){return E(E(_s7)[2]);}),_s9=B(_rN(_ga,_g8,_s8,_)),_sa=_s9,_sb=new T(function(){return E(E(_sa)[2]);}),_sc=B(_rN(_g7,_g5,_sb,_)),_sd=_sc,_se=E(_rM),_sf=jsQuerySelectorAll(_se,toJSStr(_rp)),_sg=new T(function(){return E(E(_sd)[2]);}),_sh=B(_pf(_sf,_qs,_sg,_)),_si=_sh,_sj=new T(function(){return E(E(_si)[2]);}),_sk=B(_rN(_g3,_g1,_sj,_)),_sl=_sk,_sm=new T(function(){return E(E(_sl)[2]);}),_sn=B(_rN(_g0,_fY,_sm,_)),_so=_sn,_sp=jsQuerySelectorAll(_se,toJSStr(_rA)),_sq=new T(function(){return E(E(_so)[2]);}),_sr=B(_pv(_sp,_qs,_sq,_)),_ss=_sr,_st=new T(function(){return E(E(_ss)[2]);});_rG=_rL[2];_rH=_st;return null;}})(_rG,_rH,_);if(_rI!=null){return _rI;}}},_su=new T(function(){return E(E(_rE)[2]);}),_sv=B(_rF(_qr[2],_su,_)),_sw=_sv,_sx=jsQuerySelectorAll(_qo,toJSStr(E(_fU))),_sy=new T(function(){return E(E(_qp)[2]);});if(!_sx[0]){var _sz=new T(function(){return E(E(_sw)[2]);});return [0,_9W,_sz];}else{var _sA=E(_sx[1]),_sB=E(_fT),_sC=jsQuerySelectorAll(_sA,toJSStr(_sB)),_sD=new T(function(){return E(E(_sw)[2]);}),_sE=B(_pS(_sC,_sy,_sD,_)),_sF=_sE,_sG=E(_fW),_sH=jsQuerySelectorAll(_sA,toJSStr(_sG)),_sI=new T(function(){return E(E(_sF)[2]);}),_sJ=B(_q7(_sH,_sy,_sI,_)),_sK=_sJ,_sL=function(_sM,_sN,_){while(1){var _sO=(function(_sP,_sQ,_){var _sR=E(_sP);if(!_sR[0]){return [0,_9W,_sQ];}else{var _sS=E(_sR[1]),_sT=jsQuerySelectorAll(_sS,toJSStr(_sB)),_sU=B(_pS(_sT,_sy,_sQ,_)),_sV=_sU,_sW=jsQuerySelectorAll(_sS,toJSStr(_sG)),_sX=new T(function(){return E(E(_sV)[2]);}),_sY=B(_q7(_sW,_sy,_sX,_)),_sZ=_sY,_t0=new T(function(){return E(E(_sZ)[2]);});_sM=_sR[2];_sN=_t0;return null;}})(_sM,_sN,_);if(_sO!=null){return _sO;}}},_t1=new T(function(){return E(E(_sK)[2]);});return new F(function(){return _sL(_sx[2],_t1,_);});}}},_t2=function(_t3,_t4,_t5,_){var _t6=B(A(_hM,[_w,_pe,_t3,_fn,_t5,_])),_t7=_t6,_t8=new T(function(){return E(E(_t7)[2]);}),_t9=new T(function(){return B(_1t(E(_t7)[1],_t4));});return new F(function(){return A(_fo,[_w,_pe,_t3,_fn,_t9,_t8,_]);});},_ta=function(_tb){return new F(function(){return _jY("Main.hs:(158,35)-(164,30)|lambda");});},_tc=new T(function(){return B(_ta(_));}),_td=function(_te){return new F(function(){return _jY("Main.hs:(152,35)-(154,41)|lambda");});},_tf=new T(function(){return B(_td(_));}),_tg=function(_th){return new F(function(){return _jY("Main.hs:(148,36)-(150,42)|lambda");});},_ti=new T(function(){return B(_tg(_));}),_tj=new T(function(){return B(_ka("ww_sAKp Int"));}),_tk=function(_tl,_tm,_tn,_to,_){var _tp=rMV(_tm),_tq=E(_tl),_tr=jsQuerySelectorAll(_tq,toJSStr(E(_fV))),_ts=E(E(_tp)[7]),_tt=_ts[1],_tu=_ts[2];if(!_tr[0]){return E(_ti);}else{var _tv=_tr[1];if(!E(_tr[2])[0]){var _tw=function(_tx,_ty,_){while(1){var _tz=(function(_tA,_tB,_){var _tC=E(_tA);if(!_tC[0]){return [0,_9W,_tB];}else{var _tD=B(_t2(_tv,_iW,_tB,_)),_tE=_tD,_tF=new T(function(){return E(E(_tE)[2]);});_tx=_tC[2];_ty=_tF;return null;}})(_tx,_ty,_);if(_tz!=null){return _tz;}}},_tG=B(_tw(_tt,_to,_)),_tH=_tG,_tI=jsQuerySelectorAll(_tq,toJSStr(E(_fU)));if(!_tI[0]){return E(_tf);}else{var _tJ=_tI[1];if(!E(_tI[2])[0]){var _tK=function(_tL,_tM,_){while(1){var _tN=(function(_tO,_tP,_){var _tQ=E(_tO);if(!_tQ[0]){return [0,_9W,_tP];}else{var _tR=B(_t2(_tJ,_iw,_tP,_)),_tS=_tR,_tT=new T(function(){return E(E(_tS)[2]);});_tL=_tQ[2];_tM=_tT;return null;}})(_tL,_tM,_);if(_tN!=null){return _tN;}}},_tU=new T(function(){return E(E(_tH)[2]);}),_tV=B(_tK(_tu,_tU,_)),_tW=_tV,_tX=new T(function(){return E(E(_tW)[2]);}),_tY=B(_qn(_tq,[0,_tt,_tu,_tj],_tX,_)),_tZ=_tY,_u0=jsQuerySelectorAll(_tq,toJSStr(E(_iX)));if(!_u0[0]){return E(_tc);}else{if(!E(_u0[2])[0]){var _u1=function(_u2,_){var _u3=rMV(_tm),_u4=E(_u3),_u5=E(_u4[7]),_u6=B(_dt(_u5[1],_u5[2],_u5[3],_)),_=wMV(_tm,[0,_u4[1],_u4[2],_u4[3],_u4[4],_u4[5],_u4[6],E(_u6)[2]]),_u7=B(A(_tn,[_])),_u8=rMV(_tm),_u9=_u8,_ua=new T(function(){return E(E(_u9)[7]);});return new F(function(){return _ge(_tq,_ua,_);});},_ub=B(A(_kp,[_3b,_w,_4R,_u0[1],_hx,_u1,_])),_uc=new T(function(){return E(E(_tZ)[2]);});return [0,_9W,_uc];}else{return E(_tc);}}}else{return E(_tf);}}}else{return E(_ti);}}},_ud=function(_){return new F(function(){return _jY("Main.hs:(252,70)-(254,40)|lambda");});},_ue=function(_uf,_ug,_uh){while(1){var _ui=E(_uh);if(!_ui[0]){var _uj=_ui[4],_uk=_ui[5],_ul=E(_ui[2]),_um=E(_ul[1]);if(_uf>=_um){if(_uf!=_um){_uh=_uk;continue;}else{var _un=E(_ug),_uo=E(_ul[2]);if(_un>=_uo){if(_un!=_uo){_ug=_un;_uh=_uk;continue;}else{return E(_ui[3]);}}else{_ug=_un;_uh=_uj;continue;}}}else{_uh=_uj;continue;}}else{return E(_ne);}}},_up=new T(function(){return B(unCStr("@"));}),_uq=new T(function(){return B(unCStr("&nbsp;"));}),_ur=new T(function(){return B(_1t(_uq,_up));}),_us=function(_ut){var _uu=E(_ut);if(_uu==1){return E(_ur);}else{var _uv=new T(function(){return B(_us(_uu-1|0));},1);return new F(function(){return _1t(_uq,_uv);});}},_uw="dungeon-field",_ux="dungeon-battle",_uy=function(_uz,_){while(1){var _uA=E(_uz);if(!_uA[0]){return _9W;}else{var _uB=B(A(_fo,[_w,_3a,_uA[1],_fn,_17,_]));_uz=_uA[2];continue;}}},_uC=function(_uD,_){while(1){var _uE=E(_uD);if(!_uE[0]){return _9W;}else{var _uF=B(A(_fo,[_w,_3a,_uE[1],_fn,_17,_]));_uD=_uE[2];continue;}}},_uG=0,_uH=new T(function(){return document;}),_uI=function(){ $('#tabs a[href="#dungeon"]').tab('show'); },_uJ=function(){ $('#tabs a[href="#dungeon-battle"]').tab('show'); },_uK=(function(e){return e.parentNode;}),_uL=function(_uM){while(1){var _uN=E(_uM);if(!_uN[0]){return true;}else{if(E(_uN[1])>0){return false;}else{_uM=_uN[2];continue;}}}},_uO=new T(function(){return B(unCStr("<br>"));}),_uP=function(_uQ,_uR){if(_uQ<=_uR){var _uS=function(_uT){var _uU=new T(function(){if(_uT!=_uR){return B(_uS(_uT+1|0));}else{return [0];}});return [1,_uT,_uU];};return new F(function(){return _uS(_uQ);});}else{return [0];}},_uV=new T(function(){return B(_uP(0,34));}),_uW=new T(function(){return B(_uP(0,44));}),_uX=function(_uY){var _uZ=E(_uY);if(!_uZ[0]){return [0];}else{var _v0=_uZ[2],_v1=E(_uZ[1]);if(E(_v1)==32){var _v2=new T(function(){return B(_uX(_v0));},1);return new F(function(){return _1t(_uq,_v2);});}else{var _v3=new T(function(){return B(_uX(_v0));},1);return new F(function(){return _1t([1,_v1,_17],_v3);});}}},_v4=function(_v5){var _v6=E(_v5);if(!_v6[0]){return [0];}else{var _v7=_v6[2],_v8=new T(function(){return B(_v4(_v7));},1);return new F(function(){return _1t(_v6[1],_v8);});}},_v9=function(_va,_vb){var _vc=E(_vb);if(!_vc[0]){return [0];}else{var _vd=_vc[1],_ve=_vc[2],_vf=new T(function(){return B(_v9(_va,_ve));}),_vg=new T(function(){return B(A(_va,[_vd]));});return [1,_vg,_vf];}},_vh=function(_vi,_vj){var _vk=E(_vj);if(!_vk[0]){return [0];}else{var _vl=_vk[2],_vm=new T(function(){return B(_vh(_vi,_vl));});return [1,_vi,[1,_vk[1],_vm]];}},_vn=function(_vo){var _vp=function(_vq){var _vr=function(_vs,_vt){var _vu=E(_vs);if(!_vu[0]){return [0];}else{var _vv=_vu[1],_vw=_vu[2],_vx=E(_vt);if(_vx==1){var _vy=new T(function(){return B(_ue(E(_vv),_vq,_vo));});return [1,_vy,_17];}else{var _vz=new T(function(){return B(_vr(_vw,_vx-1|0));}),_vA=new T(function(){return B(_ue(E(_vv),_vq,_vo));});return [1,_vA,_vz];}}};return new F(function(){return _vr(_uW,45);});},_vB=B(_v9(_vp,_uV));if(!_vB[0]){return [0];}else{var _vC=_vB[2],_vD=new T(function(){return B(_vh(_uO,_vC));});return new F(function(){return _uX(B(_v4([1,_vB[1],_vD])));});}},_vE=[1],_vF=new T(function(){return B(unCStr("Failure in Data.Map.balanceL"));}),_vG=function(_vH){return new F(function(){return err(_vF);});},_vI=new T(function(){return B(_vG(_));}),_vJ=function(_vK,_vL,_vM,_vN){var _vO=E(_vN);if(!_vO[0]){var _vP=_vO[1],_vQ=E(_vM);if(!_vQ[0]){var _vR=_vQ[1],_vS=_vQ[2],_vT=_vQ[3];if(_vR<=(imul(3,_vP)|0)){return [0,(1+_vR|0)+_vP|0,E(_vK),_vL,E(_vQ),E(_vO)];}else{var _vU=E(_vQ[4]);if(!_vU[0]){var _vV=_vU[1],_vW=E(_vQ[5]);if(!_vW[0]){var _vX=_vW[1],_vY=_vW[2],_vZ=_vW[3],_w0=_vW[4],_w1=_vW[5];if(_vX>=(imul(2,_vV)|0)){var _w2=function(_w3){var _w4=E(_w1);return (_w4[0]==0)?[0,(1+_vR|0)+_vP|0,E(_vY),_vZ,[0,(1+_vV|0)+_w3|0,E(_vS),_vT,E(_vU),E(_w0)],[0,(1+_vP|0)+_w4[1]|0,E(_vK),_vL,E(_w4),E(_vO)]]:[0,(1+_vR|0)+_vP|0,E(_vY),_vZ,[0,(1+_vV|0)+_w3|0,E(_vS),_vT,E(_vU),E(_w0)],[0,1+_vP|0,E(_vK),_vL,E(_vE),E(_vO)]];},_w5=E(_w0);if(!_w5[0]){return new F(function(){return _w2(_w5[1]);});}else{return new F(function(){return _w2(0);});}}else{return [0,(1+_vR|0)+_vP|0,E(_vS),_vT,E(_vU),[0,(1+_vP|0)+_vX|0,E(_vK),_vL,E(_vW),E(_vO)]];}}else{return E(_vI);}}else{return E(_vI);}}}else{return [0,1+_vP|0,E(_vK),_vL,E(_vE),E(_vO)];}}else{var _w6=E(_vM);if(!_w6[0]){var _w7=_w6[1],_w8=_w6[2],_w9=_w6[3],_wa=_w6[5],_wb=E(_w6[4]);if(!_wb[0]){var _wc=_wb[1],_wd=E(_wa);if(!_wd[0]){var _we=_wd[1],_wf=_wd[2],_wg=_wd[3],_wh=_wd[4],_wi=_wd[5];if(_we>=(imul(2,_wc)|0)){var _wj=function(_wk){var _wl=E(_wi);return (_wl[0]==0)?[0,1+_w7|0,E(_wf),_wg,[0,(1+_wc|0)+_wk|0,E(_w8),_w9,E(_wb),E(_wh)],[0,1+_wl[1]|0,E(_vK),_vL,E(_wl),E(_vE)]]:[0,1+_w7|0,E(_wf),_wg,[0,(1+_wc|0)+_wk|0,E(_w8),_w9,E(_wb),E(_wh)],[0,1,E(_vK),_vL,E(_vE),E(_vE)]];},_wm=E(_wh);if(!_wm[0]){return new F(function(){return _wj(_wm[1]);});}else{return new F(function(){return _wj(0);});}}else{return [0,1+_w7|0,E(_w8),_w9,E(_wb),[0,1+_we|0,E(_vK),_vL,E(_wd),E(_vE)]];}}else{return [0,3,E(_w8),_w9,E(_wb),[0,1,E(_vK),_vL,E(_vE),E(_vE)]];}}else{var _wn=E(_wa);return (_wn[0]==0)?[0,3,E(_wn[2]),_wn[3],[0,1,E(_w8),_w9,E(_vE),E(_vE)],[0,1,E(_vK),_vL,E(_vE),E(_vE)]]:[0,2,E(_vK),_vL,E(_w6),E(_vE)];}}else{return [0,1,E(_vK),_vL,E(_vE),E(_vE)];}}},_wo=new T(function(){return B(unCStr("Failure in Data.Map.balanceR"));}),_wp=function(_wq){return new F(function(){return err(_wo);});},_wr=new T(function(){return B(_wp(_));}),_ws=function(_wt,_wu,_wv,_ww){var _wx=E(_wv);if(!_wx[0]){var _wy=_wx[1],_wz=E(_ww);if(!_wz[0]){var _wA=_wz[1],_wB=_wz[2],_wC=_wz[3];if(_wA<=(imul(3,_wy)|0)){return [0,(1+_wy|0)+_wA|0,E(_wt),_wu,E(_wx),E(_wz)];}else{var _wD=E(_wz[4]);if(!_wD[0]){var _wE=_wD[1],_wF=_wD[2],_wG=_wD[3],_wH=_wD[4],_wI=_wD[5],_wJ=E(_wz[5]);if(!_wJ[0]){var _wK=_wJ[1];if(_wE>=(imul(2,_wK)|0)){var _wL=function(_wM){var _wN=E(_wt),_wO=E(_wI);return (_wO[0]==0)?[0,(1+_wy|0)+_wA|0,E(_wF),_wG,[0,(1+_wy|0)+_wM|0,E(_wN),_wu,E(_wx),E(_wH)],[0,(1+_wK|0)+_wO[1]|0,E(_wB),_wC,E(_wO),E(_wJ)]]:[0,(1+_wy|0)+_wA|0,E(_wF),_wG,[0,(1+_wy|0)+_wM|0,E(_wN),_wu,E(_wx),E(_wH)],[0,1+_wK|0,E(_wB),_wC,E(_vE),E(_wJ)]];},_wP=E(_wH);if(!_wP[0]){return new F(function(){return _wL(_wP[1]);});}else{return new F(function(){return _wL(0);});}}else{return [0,(1+_wy|0)+_wA|0,E(_wB),_wC,[0,(1+_wy|0)+_wE|0,E(_wt),_wu,E(_wx),E(_wD)],E(_wJ)];}}else{return E(_wr);}}else{return E(_wr);}}}else{return [0,1+_wy|0,E(_wt),_wu,E(_wx),E(_vE)];}}else{var _wQ=E(_ww);if(!_wQ[0]){var _wR=_wQ[1],_wS=_wQ[2],_wT=_wQ[3],_wU=_wQ[5],_wV=E(_wQ[4]);if(!_wV[0]){var _wW=_wV[1],_wX=_wV[2],_wY=_wV[3],_wZ=_wV[4],_x0=_wV[5],_x1=E(_wU);if(!_x1[0]){var _x2=_x1[1];if(_wW>=(imul(2,_x2)|0)){var _x3=function(_x4){var _x5=E(_wt),_x6=E(_x0);return (_x6[0]==0)?[0,1+_wR|0,E(_wX),_wY,[0,1+_x4|0,E(_x5),_wu,E(_vE),E(_wZ)],[0,(1+_x2|0)+_x6[1]|0,E(_wS),_wT,E(_x6),E(_x1)]]:[0,1+_wR|0,E(_wX),_wY,[0,1+_x4|0,E(_x5),_wu,E(_vE),E(_wZ)],[0,1+_x2|0,E(_wS),_wT,E(_vE),E(_x1)]];},_x7=E(_wZ);if(!_x7[0]){return new F(function(){return _x3(_x7[1]);});}else{return new F(function(){return _x3(0);});}}else{return [0,1+_wR|0,E(_wS),_wT,[0,1+_wW|0,E(_wt),_wu,E(_vE),E(_wV)],E(_x1)];}}else{return [0,3,E(_wX),_wY,[0,1,E(_wt),_wu,E(_vE),E(_vE)],[0,1,E(_wS),_wT,E(_vE),E(_vE)]];}}else{var _x8=E(_wU);return (_x8[0]==0)?[0,3,E(_wS),_wT,[0,1,E(_wt),_wu,E(_vE),E(_vE)],E(_x8)]:[0,2,E(_wt),_wu,E(_vE),E(_wQ)];}}else{return [0,1,E(_wt),_wu,E(_vE),E(_vE)];}}},_x9=function(_xa){return E(E(_xa)[2]);},_xb=function(_xc,_xd,_xe,_xf){var _xg=E(_xd),_xh=E(_xf);if(!_xh[0]){var _xi=_xh[2],_xj=_xh[3],_xk=_xh[4],_xl=_xh[5];switch(B(A(_x9,[_xc,_xg,_xi]))){case 0:return new F(function(){return _vJ(_xi,_xj,B(_xb(_xc,_xg,_xe,_xk)),_xl);});break;case 1:return [0,_xh[1],E(_xg),_xe,E(_xk),E(_xl)];default:return new F(function(){return _ws(_xi,_xj,_xk,B(_xb(_xc,_xg,_xe,_xl)));});}}else{return [0,1,E(_xg),_xe,E(_vE),E(_vE)];}},_xm=function(_xn,_xo,_xp,_xq){return new F(function(){return _xb(_xn,_xo,_xp,_xq);});},_xr=function(_xs,_xt,_xu){var _xv=function(_xw){var _xx=E(_xw);if(!_xx[0]){return E(_xu);}else{var _xy=E(_xx[1]);return new F(function(){return _xm(_xs,_xy[1],_xy[2],B(_xv(_xx[2])));});}};return new F(function(){return _xv(_xt);});},_xz=function(_xA){return E(E(_xA)[10]);},_xB=new T(function(){return B(unCStr("block"));}),_xC=new T(function(){return B(unCStr("display"));}),_xD=function(_xE){return new F(function(){return _jY("Main.hs:(242,64)-(244,35)|lambda");});},_xF=new T(function(){return B(_xD(_));}),_xG=[1,_17,_17],_xH=function(_xI){var _xJ=E(_xI);if(!_xJ[0]){return E(_xG);}else{var _xK=_xJ[2],_xL=new T(function(){return B(_xH(_xK));}),_xM=function(_xN){var _xO=E(_xN);if(!_xO[0]){return [0];}else{var _xP=_xO[1],_xQ=_xO[2],_xR=new T(function(){return B(_xM(_xQ));}),_xS=function(_xT){var _xU=E(_xT);if(!_xU[0]){return E(_xR);}else{var _xV=_xU[2],_xW=new T(function(){return B(_xS(_xV));});return [1,[1,_xP,_xU[1]],_xW];}};return new F(function(){return _xS(_xL);});}};return new F(function(){return _xM(_xJ[1]);});}},_xX=function(_xY,_xZ){if(0>=_xY){return E(_xG);}else{var _y0=[1,_xZ,_17],_y1=function(_y2){var _y3=E(_y2);if(_y3==1){return E(_y0);}else{var _y4=new T(function(){return B(_y1(_y3-1|0));});return [1,_xZ,_y4];}};return new F(function(){return _xH(B(_y1(_xY)));});}},_y5=-2,_y6=-1,_y7=1,_y8=2,_y9=[1,_y8,_17],_ya=[1,_y7,_y9],_yb=[1,_uG,_ya],_yc=[1,_y6,_yb],_yd=[1,_y5,_yc],_ye=new T(function(){return B(_xX(2,_yd));}),_yf=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:230:3-9"));}),_yg=[0,_31,_32,_17,_yf,_31,_31],_yh=new T(function(){return B(_2Z(_yg));}),_yi=new T(function(){return B(unCStr("none"));}),_yj=new T(function(){return B(unCStr("#tabs a[href=\"#dungeon-battle\"]"));}),_yk=new T(function(){return B(unCStr("player"));}),_yl=new T(function(){return B(unCStr(" found!"));}),_ym=function(_yn){var _yo=new T(function(){return B(_1t(fromJSStr(E(_yn)),_yl));});return new F(function(){return err(B(unAppCStr("No element with ID ",_yo)));});},_yp=function(_yq,_yr,_ys,_yt,_yu,_yv,_yw,_){var _yx=E(_ys),_yy=_yx[1],_yz=_yx[2],_yA=function(_,_yB,_yC,_yD,_yE,_yF,_yG,_yH,_yI){var _yJ=function(_,_yK,_yL,_yM,_yN,_yO,_yP,_yQ,_yR){var _yS=function(_,_yT,_yU,_yV,_yW,_yX,_yY,_yZ,_z0){var _z1=function(_,_z2,_z3,_z4,_z5,_z6,_z7,_z8,_z9){var _za=jsFind(toJSStr(E(_yk)));if(!_za[0]){return new F(function(){return die(_yh);});}else{var _zb=new T(function(){var _zc=function(_zd){while(1){var _ze=(function(_zf){var _zg=E(_zf);if(!_zg[0]){return [0];}else{var _zh=_zg[2],_zi=E(_zg[1]);if(!_zi[0]){_zd=_zh;return null;}else{var _zj=E(_zi[2]);if(!_zj[0]){_zd=_zh;return null;}else{if(!E(_zj[2])[0]){var _zk=E(_z3),_zl=E(_zi[1]);if(0>(_zk+_zl|0)){var _zm=function(_zn){while(1){var _zo=(function(_zp){var _zq=E(_zp);if(!_zq[0]){return [0];}else{var _zr=_zq[2],_zs=E(_zq[1]);if(!_zs[0]){_zn=_zr;return null;}else{var _zt=E(_zs[2]);if(!_zt[0]){_zn=_zr;return null;}else{if(!E(_zt[2])[0]){var _zu=E(_zs[1]);if(0>(_zk+_zu|0)){_zn=_zr;return null;}else{if((_zk+_zu|0)>44){_zn=_zr;return null;}else{var _zv=E(_z4),_zw=E(_zt[1]);if(0>(_zv+_zw|0)){_zn=_zr;return null;}else{if((_zv+_zw|0)>34){_zn=_zr;return null;}else{var _zx=new T(function(){return B(_zm(_zr));}),_zy=_zk+_zu|0,_zz=_zv+_zw|0,_zA=new T(function(){return B(_nf(_zy,_zz,_z6));});return [1,[0,[0,_zy,_zz],_zA],_zx];}}}}}else{_zn=_zr;return null;}}}}})(_zn);if(_zo!=null){return _zo;}}};return new F(function(){return _zm(_zh);});}else{if((_zk+_zl|0)>44){var _zB=function(_zC){while(1){var _zD=(function(_zE){var _zF=E(_zE);if(!_zF[0]){return [0];}else{var _zG=_zF[2],_zH=E(_zF[1]);if(!_zH[0]){_zC=_zG;return null;}else{var _zI=E(_zH[2]);if(!_zI[0]){_zC=_zG;return null;}else{if(!E(_zI[2])[0]){var _zJ=E(_zH[1]);if(0>(_zk+_zJ|0)){_zC=_zG;return null;}else{if((_zk+_zJ|0)>44){_zC=_zG;return null;}else{var _zK=E(_z4),_zL=E(_zI[1]);if(0>(_zK+_zL|0)){_zC=_zG;return null;}else{if((_zK+_zL|0)>34){_zC=_zG;return null;}else{var _zM=new T(function(){return B(_zB(_zG));}),_zN=_zk+_zJ|0,_zO=_zK+_zL|0,_zP=new T(function(){return B(_nf(_zN,_zO,_z6));});return [1,[0,[0,_zN,_zO],_zP],_zM];}}}}}else{_zC=_zG;return null;}}}}})(_zC);if(_zD!=null){return _zD;}}};return new F(function(){return _zB(_zh);});}else{var _zQ=E(_z4),_zR=E(_zj[1]);if(0>(_zQ+_zR|0)){var _zS=function(_zT){while(1){var _zU=(function(_zV){var _zW=E(_zV);if(!_zW[0]){return [0];}else{var _zX=_zW[2],_zY=E(_zW[1]);if(!_zY[0]){_zT=_zX;return null;}else{var _zZ=E(_zY[2]);if(!_zZ[0]){_zT=_zX;return null;}else{if(!E(_zZ[2])[0]){var _A0=E(_zY[1]);if(0>(_zk+_A0|0)){_zT=_zX;return null;}else{if((_zk+_A0|0)>44){_zT=_zX;return null;}else{var _A1=E(_zZ[1]);if(0>(_zQ+_A1|0)){_zT=_zX;return null;}else{if((_zQ+_A1|0)>34){_zT=_zX;return null;}else{var _A2=new T(function(){return B(_zS(_zX));}),_A3=_zk+_A0|0,_A4=_zQ+_A1|0,_A5=new T(function(){return B(_nf(_A3,_A4,_z6));});return [1,[0,[0,_A3,_A4],_A5],_A2];}}}}}else{_zT=_zX;return null;}}}}})(_zT);if(_zU!=null){return _zU;}}};return new F(function(){return _zS(_zh);});}else{if((_zQ+_zR|0)>34){var _A6=function(_A7){while(1){var _A8=(function(_A9){var _Aa=E(_A9);if(!_Aa[0]){return [0];}else{var _Ab=_Aa[2],_Ac=E(_Aa[1]);if(!_Ac[0]){_A7=_Ab;return null;}else{var _Ad=E(_Ac[2]);if(!_Ad[0]){_A7=_Ab;return null;}else{if(!E(_Ad[2])[0]){var _Ae=E(_Ac[1]);if(0>(_zk+_Ae|0)){_A7=_Ab;return null;}else{if((_zk+_Ae|0)>44){_A7=_Ab;return null;}else{var _Af=E(_Ad[1]);if(0>(_zQ+_Af|0)){_A7=_Ab;return null;}else{if((_zQ+_Af|0)>34){_A7=_Ab;return null;}else{var _Ag=new T(function(){return B(_A6(_Ab));}),_Ah=_zk+_Ae|0,_Ai=_zQ+_Af|0,_Aj=new T(function(){return B(_nf(_Ah,_Ai,_z6));});return [1,[0,[0,_Ah,_Ai],_Aj],_Ag];}}}}}else{_A7=_Ab;return null;}}}}})(_A7);if(_A8!=null){return _A8;}}};return new F(function(){return _A6(_zh);});}else{var _Ak=new T(function(){var _Al=function(_Am){while(1){var _An=(function(_Ao){var _Ap=E(_Ao);if(!_Ap[0]){return [0];}else{var _Aq=_Ap[2],_Ar=E(_Ap[1]);if(!_Ar[0]){_Am=_Aq;return null;}else{var _As=E(_Ar[2]);if(!_As[0]){_Am=_Aq;return null;}else{if(!E(_As[2])[0]){var _At=E(_Ar[1]);if(0>(_zk+_At|0)){_Am=_Aq;return null;}else{if((_zk+_At|0)>44){_Am=_Aq;return null;}else{var _Au=E(_As[1]);if(0>(_zQ+_Au|0)){_Am=_Aq;return null;}else{if((_zQ+_Au|0)>34){_Am=_Aq;return null;}else{var _Av=new T(function(){return B(_Al(_Aq));}),_Aw=_zk+_At|0,_Ax=_zQ+_Au|0,_Ay=new T(function(){return B(_nf(_Aw,_Ax,_z6));});return [1,[0,[0,_Aw,_Ax],_Ay],_Av];}}}}}else{_Am=_Aq;return null;}}}}})(_Am);if(_An!=null){return _An;}}};return B(_Al(_zh));}),_Az=_zk+_zl|0,_AA=_zQ+_zR|0,_AB=new T(function(){return B(_nf(_Az,_AA,_z6));});return [1,[0,[0,_Az,_AA],_AB],_Ak];}}}}}else{_zd=_zh;return null;}}}}})(_zd);if(_ze!=null){return _ze;}}};return B(_xr(_nc,B(_zc(_ye)),_z7));}),_AC=new T(function(){var _AD=E(_z4);if(0>=_AD){var _AE=E(_z3);if(0>=_AE){return E(_up);}else{return B(_us(_AE));}}else{var _AF=new T(function(){var _AG=new T(function(){var _AH=E(_z3);if(0>=_AH){return E(_up);}else{return B(_us(_AH));}},1);return B(_1t(_uO,_AG));}),_AI=function(_AJ){var _AK=E(_AJ);if(_AK==1){return E(_AF);}else{var _AL=new T(function(){return B(_AI(_AK-1|0));},1);return new F(function(){return _1t(_uO,_AL);});}};return B(_AI(_AD));}}),_AM=B(A(_fo,[_w,_pe,_za[1],_fn,_AC,[0,_z2,[0,_z3,_z4],_z5,_z6,_zb,_z8,_z9],_])),_AN=_AM,_AO=E(_uw),_AP=jsFind(_AO);if(!_AP[0]){return new F(function(){return _ym(_AO);});}else{var _AQ=new T(function(){return E(E(_AN)[2]);}),_AR=new T(function(){var _AS=new T(function(){return E(E(_AQ)[5]);});return B(_vn(_AS));}),_AT=B(A(_fo,[_w,_pe,_AP[1],_fn,_AR,_AQ,_])),_AU=E(E(_AT)[2]);if(E(_AU[6])==5){var _AV=E(_4k),_AW=E(_uJ)(_AV),_AX=E(_uH),_AY=toJSStr(E(_yj)),_AZ=jsQuerySelectorAll(_AX,_AY);if(!_AZ[0]){return E(_xF);}else{if(!E(_AZ[2])[0]){var _B0=E(_uK),_B1=_B0(E(_AZ[1])),_B2=B(A(_eL,[_w,_pe,_B1,_xC,_xB,[0,_AU[1],_AU[2],_AU[3],_AU[4],_AU[5],_uG,_AU[7]],_])),_B3=_B2,_B4=E(_ux),_B5=jsFind(_B4);if(!_B5[0]){return new F(function(){return _ym(_B4);});}else{var _B6=_B5[1],_B7=E(_yq),_B8=new T(function(){return E(E(_B3)[2]);}),_B9=function(_){var _Ba=rMV(_B7);if(!B(_uL(B(_v9(_xz,E(E(_Ba)[7])[2]))))){return _9W;}else{var _Bb=E(_uI)(_AV),_Bc=jsQuerySelectorAll(_AX,_AY);if(!_Bc[0]){return new F(function(){return _ud(_);});}else{if(!E(_Bc[2])[0]){var _Bd=_B0(E(_Bc[1])),_Be=B(A(_eL,[_w,_3a,_Bd,_xC,_yi,_])),_Bf=E(_B6),_Bg=jsQuerySelectorAll(_Bf,toJSStr(E(_fV))),_Bh=B(_uy(_Bg,_)),_Bi=jsQuerySelectorAll(_Bf,toJSStr(E(_fU)));return new F(function(){return _uC(_Bi,_);});}else{return new F(function(){return _ud(_);});}}}};return new F(function(){return _tk(_B6,_B7,_B9,_B8,_);});}}else{return E(_xF);}}}else{return [0,_9W,_AU];}}}};if(!B(_ai(_yr,39))){return new F(function(){return _z1(_,_yT,_yU,_yV,_yW,_yX,_yY,_yZ,_z0);});}else{var _Bj=E(_yU),_Bk=_Bj+1|0;switch(E(B(_ue(_Bk,_yV,_yX)))){case 35:var _Bl=new T(function(){return E(_yZ)+1|0;});return new F(function(){return _z1(_,_yT,_Bk,_yV,_yW,_yX,_yY,_Bl,_z0);});break;case 45:var _Bm=new T(function(){return E(_yZ)+1|0;});return new F(function(){return _z1(_,_yT,_Bk,_yV,_yW,_yX,_yY,_Bm,_z0);});break;default:return new F(function(){return _z1(_,_yT,_Bj,_yV,_yW,_yX,_yY,_yZ,_z0);});}}};if(!B(_ai(_yr,37))){return new F(function(){return _yS(_,_yK,_yL,_yM,_yN,_yO,_yP,_yQ,_yR);});}else{var _Bn=_yL+(-1)|0;switch(E(B(_ue(_Bn,_yM,_yO)))){case 35:var _Bo=new T(function(){return E(_yQ)+1|0;});return new F(function(){return _yS(_,_yK,_Bn,_yM,_yN,_yO,_yP,_Bo,_yR);});break;case 45:var _Bp=new T(function(){return E(_yQ)+1|0;});return new F(function(){return _yS(_,_yK,_Bn,_yM,_yN,_yO,_yP,_Bp,_yR);});break;default:return new F(function(){return _yS(_,_yK,_yL,_yM,_yN,_yO,_yP,_yQ,_yR);});}}};if(!B(_ai(_yr,40))){return new F(function(){return _yJ(_,_yB,_yC,_yD,_yE,_yF,_yG,_yH,_yI);});}else{var _Bq=new T(function(){return E(_yD)+1|0;});switch(E(B(_ue(_yC,_Bq,_yF)))){case 35:var _Br=new T(function(){return E(_yH)+1|0;});return new F(function(){return _yJ(_,_yB,_yC,_Bq,_yE,_yF,_yG,_Br,_yI);});break;case 45:var _Bs=new T(function(){return E(_yH)+1|0;});return new F(function(){return _yJ(_,_yB,_yC,_Bq,_yE,_yF,_yG,_Bs,_yI);});break;default:return new F(function(){return _yJ(_,_yB,_yC,_yD,_yE,_yF,_yG,_yH,_yI);});}}};if(!B(_ai(_yr,38))){var _Bt=function(_,_Bu,_Bv,_Bw,_Bx,_By,_Bz,_BA,_BB){var _BC=function(_,_BD,_BE,_BF,_BG,_BH,_BI,_BJ,_BK){var _BL=function(_,_BM,_BN,_BO,_BP,_BQ,_BR,_BS,_BT){var _BU=jsFind(toJSStr(E(_yk)));if(!_BU[0]){return new F(function(){return die(_yh);});}else{var _BV=new T(function(){var _BW=function(_BX){while(1){var _BY=(function(_BZ){var _C0=E(_BZ);if(!_C0[0]){return [0];}else{var _C1=_C0[2],_C2=E(_C0[1]);if(!_C2[0]){_BX=_C1;return null;}else{var _C3=E(_C2[2]);if(!_C3[0]){_BX=_C1;return null;}else{if(!E(_C3[2])[0]){var _C4=E(_BN),_C5=E(_C2[1]);if(0>(_C4+_C5|0)){var _C6=function(_C7){while(1){var _C8=(function(_C9){var _Ca=E(_C9);if(!_Ca[0]){return [0];}else{var _Cb=_Ca[2],_Cc=E(_Ca[1]);if(!_Cc[0]){_C7=_Cb;return null;}else{var _Cd=E(_Cc[2]);if(!_Cd[0]){_C7=_Cb;return null;}else{if(!E(_Cd[2])[0]){var _Ce=E(_Cc[1]);if(0>(_C4+_Ce|0)){_C7=_Cb;return null;}else{if((_C4+_Ce|0)>44){_C7=_Cb;return null;}else{var _Cf=E(_BO),_Cg=E(_Cd[1]);if(0>(_Cf+_Cg|0)){_C7=_Cb;return null;}else{if((_Cf+_Cg|0)>34){_C7=_Cb;return null;}else{var _Ch=new T(function(){return B(_C6(_Cb));}),_Ci=_C4+_Ce|0,_Cj=_Cf+_Cg|0,_Ck=new T(function(){return B(_nf(_Ci,_Cj,_BQ));});return [1,[0,[0,_Ci,_Cj],_Ck],_Ch];}}}}}else{_C7=_Cb;return null;}}}}})(_C7);if(_C8!=null){return _C8;}}};return new F(function(){return _C6(_C1);});}else{if((_C4+_C5|0)>44){var _Cl=function(_Cm){while(1){var _Cn=(function(_Co){var _Cp=E(_Co);if(!_Cp[0]){return [0];}else{var _Cq=_Cp[2],_Cr=E(_Cp[1]);if(!_Cr[0]){_Cm=_Cq;return null;}else{var _Cs=E(_Cr[2]);if(!_Cs[0]){_Cm=_Cq;return null;}else{if(!E(_Cs[2])[0]){var _Ct=E(_Cr[1]);if(0>(_C4+_Ct|0)){_Cm=_Cq;return null;}else{if((_C4+_Ct|0)>44){_Cm=_Cq;return null;}else{var _Cu=E(_BO),_Cv=E(_Cs[1]);if(0>(_Cu+_Cv|0)){_Cm=_Cq;return null;}else{if((_Cu+_Cv|0)>34){_Cm=_Cq;return null;}else{var _Cw=new T(function(){return B(_Cl(_Cq));}),_Cx=_C4+_Ct|0,_Cy=_Cu+_Cv|0,_Cz=new T(function(){return B(_nf(_Cx,_Cy,_BQ));});return [1,[0,[0,_Cx,_Cy],_Cz],_Cw];}}}}}else{_Cm=_Cq;return null;}}}}})(_Cm);if(_Cn!=null){return _Cn;}}};return new F(function(){return _Cl(_C1);});}else{var _CA=E(_BO),_CB=E(_C3[1]);if(0>(_CA+_CB|0)){var _CC=function(_CD){while(1){var _CE=(function(_CF){var _CG=E(_CF);if(!_CG[0]){return [0];}else{var _CH=_CG[2],_CI=E(_CG[1]);if(!_CI[0]){_CD=_CH;return null;}else{var _CJ=E(_CI[2]);if(!_CJ[0]){_CD=_CH;return null;}else{if(!E(_CJ[2])[0]){var _CK=E(_CI[1]);if(0>(_C4+_CK|0)){_CD=_CH;return null;}else{if((_C4+_CK|0)>44){_CD=_CH;return null;}else{var _CL=E(_CJ[1]);if(0>(_CA+_CL|0)){_CD=_CH;return null;}else{if((_CA+_CL|0)>34){_CD=_CH;return null;}else{var _CM=new T(function(){return B(_CC(_CH));}),_CN=_C4+_CK|0,_CO=_CA+_CL|0,_CP=new T(function(){return B(_nf(_CN,_CO,_BQ));});return [1,[0,[0,_CN,_CO],_CP],_CM];}}}}}else{_CD=_CH;return null;}}}}})(_CD);if(_CE!=null){return _CE;}}};return new F(function(){return _CC(_C1);});}else{if((_CA+_CB|0)>34){var _CQ=function(_CR){while(1){var _CS=(function(_CT){var _CU=E(_CT);if(!_CU[0]){return [0];}else{var _CV=_CU[2],_CW=E(_CU[1]);if(!_CW[0]){_CR=_CV;return null;}else{var _CX=E(_CW[2]);if(!_CX[0]){_CR=_CV;return null;}else{if(!E(_CX[2])[0]){var _CY=E(_CW[1]);if(0>(_C4+_CY|0)){_CR=_CV;return null;}else{if((_C4+_CY|0)>44){_CR=_CV;return null;}else{var _CZ=E(_CX[1]);if(0>(_CA+_CZ|0)){_CR=_CV;return null;}else{if((_CA+_CZ|0)>34){_CR=_CV;return null;}else{var _D0=new T(function(){return B(_CQ(_CV));}),_D1=_C4+_CY|0,_D2=_CA+_CZ|0,_D3=new T(function(){return B(_nf(_D1,_D2,_BQ));});return [1,[0,[0,_D1,_D2],_D3],_D0];}}}}}else{_CR=_CV;return null;}}}}})(_CR);if(_CS!=null){return _CS;}}};return new F(function(){return _CQ(_C1);});}else{var _D4=new T(function(){var _D5=function(_D6){while(1){var _D7=(function(_D8){var _D9=E(_D8);if(!_D9[0]){return [0];}else{var _Da=_D9[2],_Db=E(_D9[1]);if(!_Db[0]){_D6=_Da;return null;}else{var _Dc=E(_Db[2]);if(!_Dc[0]){_D6=_Da;return null;}else{if(!E(_Dc[2])[0]){var _Dd=E(_Db[1]);if(0>(_C4+_Dd|0)){_D6=_Da;return null;}else{if((_C4+_Dd|0)>44){_D6=_Da;return null;}else{var _De=E(_Dc[1]);if(0>(_CA+_De|0)){_D6=_Da;return null;}else{if((_CA+_De|0)>34){_D6=_Da;return null;}else{var _Df=new T(function(){return B(_D5(_Da));}),_Dg=_C4+_Dd|0,_Dh=_CA+_De|0,_Di=new T(function(){return B(_nf(_Dg,_Dh,_BQ));});return [1,[0,[0,_Dg,_Dh],_Di],_Df];}}}}}else{_D6=_Da;return null;}}}}})(_D6);if(_D7!=null){return _D7;}}};return B(_D5(_C1));}),_Dj=_C4+_C5|0,_Dk=_CA+_CB|0,_Dl=new T(function(){return B(_nf(_Dj,_Dk,_BQ));});return [1,[0,[0,_Dj,_Dk],_Dl],_D4];}}}}}else{_BX=_C1;return null;}}}}})(_BX);if(_BY!=null){return _BY;}}};return B(_xr(_nc,B(_BW(_ye)),_BR));}),_Dm=new T(function(){var _Dn=E(_BO);if(0>=_Dn){var _Do=E(_BN);if(0>=_Do){return E(_up);}else{return B(_us(_Do));}}else{var _Dp=new T(function(){var _Dq=new T(function(){var _Dr=E(_BN);if(0>=_Dr){return E(_up);}else{return B(_us(_Dr));}},1);return B(_1t(_uO,_Dq));}),_Ds=function(_Dt){var _Du=E(_Dt);if(_Du==1){return E(_Dp);}else{var _Dv=new T(function(){return B(_Ds(_Du-1|0));},1);return new F(function(){return _1t(_uO,_Dv);});}};return B(_Ds(_Dn));}}),_Dw=B(A(_fo,[_w,_pe,_BU[1],_fn,_Dm,[0,_BM,[0,_BN,_BO],_BP,_BQ,_BV,_BS,_BT],_])),_Dx=_Dw,_Dy=E(_uw),_Dz=jsFind(_Dy);if(!_Dz[0]){return new F(function(){return _ym(_Dy);});}else{var _DA=new T(function(){return E(E(_Dx)[2]);}),_DB=new T(function(){var _DC=new T(function(){return E(E(_DA)[5]);});return B(_vn(_DC));}),_DD=B(A(_fo,[_w,_pe,_Dz[1],_fn,_DB,_DA,_])),_DE=E(E(_DD)[2]);if(E(_DE[6])==5){var _DF=E(_4k),_DG=E(_uJ)(_DF),_DH=E(_uH),_DI=toJSStr(E(_yj)),_DJ=jsQuerySelectorAll(_DH,_DI);if(!_DJ[0]){return E(_xF);}else{if(!E(_DJ[2])[0]){var _DK=E(_uK),_DL=_DK(E(_DJ[1])),_DM=B(A(_eL,[_w,_pe,_DL,_xC,_xB,[0,_DE[1],_DE[2],_DE[3],_DE[4],_DE[5],_uG,_DE[7]],_])),_DN=_DM,_DO=E(_ux),_DP=jsFind(_DO);if(!_DP[0]){return new F(function(){return _ym(_DO);});}else{var _DQ=_DP[1],_DR=E(_yq),_DS=new T(function(){return E(E(_DN)[2]);}),_DT=function(_){var _DU=rMV(_DR);if(!B(_uL(B(_v9(_xz,E(E(_DU)[7])[2]))))){return _9W;}else{var _DV=E(_uI)(_DF),_DW=jsQuerySelectorAll(_DH,_DI);if(!_DW[0]){return new F(function(){return _ud(_);});}else{if(!E(_DW[2])[0]){var _DX=_DK(E(_DW[1])),_DY=B(A(_eL,[_w,_3a,_DX,_xC,_yi,_])),_DZ=E(_DQ),_E0=jsQuerySelectorAll(_DZ,toJSStr(E(_fV))),_E1=B(_uy(_E0,_)),_E2=jsQuerySelectorAll(_DZ,toJSStr(E(_fU)));return new F(function(){return _uC(_E2,_);});}else{return new F(function(){return _ud(_);});}}}};return new F(function(){return _tk(_DQ,_DR,_DT,_DS,_);});}}else{return E(_xF);}}}else{return [0,_9W,_DE];}}}};if(!B(_ai(_yr,39))){return new F(function(){return _BL(_,_BD,_BE,_BF,_BG,_BH,_BI,_BJ,_BK);});}else{var _E3=_BE+1|0;switch(E(B(_ue(_E3,_BF,_BH)))){case 35:var _E4=new T(function(){return E(_BJ)+1|0;});return new F(function(){return _BL(_,_BD,_E3,_BF,_BG,_BH,_BI,_E4,_BK);});break;case 45:var _E5=new T(function(){return E(_BJ)+1|0;});return new F(function(){return _BL(_,_BD,_E3,_BF,_BG,_BH,_BI,_E5,_BK);});break;default:return new F(function(){return _BL(_,_BD,_BE,_BF,_BG,_BH,_BI,_BJ,_BK);});}}};if(!B(_ai(_yr,37))){return new F(function(){return _BC(_,_Bu,_Bv,_Bw,_Bx,_By,_Bz,_BA,_BB);});}else{var _E6=_Bv+(-1)|0;switch(E(B(_ue(_E6,_Bw,_By)))){case 35:var _E7=new T(function(){return E(_BA)+1|0;});return new F(function(){return _BC(_,_Bu,_E6,_Bw,_Bx,_By,_Bz,_E7,_BB);});break;case 45:var _E8=new T(function(){return E(_BA)+1|0;});return new F(function(){return _BC(_,_Bu,_E6,_Bw,_Bx,_By,_Bz,_E8,_BB);});break;default:return new F(function(){return _BC(_,_Bu,_Bv,_Bw,_Bx,_By,_Bz,_BA,_BB);});}}};if(!B(_ai(_yr,40))){var _E9=function(_,_Ea,_Eb,_Ec,_Ed,_Ee,_Ef,_Eg,_Eh){var _Ei=function(_,_Ej,_Ek,_El,_Em,_En,_Eo,_Ep,_Eq){var _Er=jsFind(toJSStr(E(_yk)));if(!_Er[0]){return new F(function(){return die(_yh);});}else{var _Es=new T(function(){var _Et=function(_Eu){while(1){var _Ev=(function(_Ew){var _Ex=E(_Ew);if(!_Ex[0]){return [0];}else{var _Ey=_Ex[2],_Ez=E(_Ex[1]);if(!_Ez[0]){_Eu=_Ey;return null;}else{var _EA=E(_Ez[2]);if(!_EA[0]){_Eu=_Ey;return null;}else{if(!E(_EA[2])[0]){var _EB=E(_Ez[1]);if(0>(_Ek+_EB|0)){var _EC=function(_ED){while(1){var _EE=(function(_EF){var _EG=E(_EF);if(!_EG[0]){return [0];}else{var _EH=_EG[2],_EI=E(_EG[1]);if(!_EI[0]){_ED=_EH;return null;}else{var _EJ=E(_EI[2]);if(!_EJ[0]){_ED=_EH;return null;}else{if(!E(_EJ[2])[0]){var _EK=E(_EI[1]);if(0>(_Ek+_EK|0)){_ED=_EH;return null;}else{if((_Ek+_EK|0)>44){_ED=_EH;return null;}else{var _EL=E(_El),_EM=E(_EJ[1]);if(0>(_EL+_EM|0)){_ED=_EH;return null;}else{if((_EL+_EM|0)>34){_ED=_EH;return null;}else{var _EN=new T(function(){return B(_EC(_EH));}),_EO=_Ek+_EK|0,_EP=_EL+_EM|0,_EQ=new T(function(){return B(_nf(_EO,_EP,_En));});return [1,[0,[0,_EO,_EP],_EQ],_EN];}}}}}else{_ED=_EH;return null;}}}}})(_ED);if(_EE!=null){return _EE;}}};return new F(function(){return _EC(_Ey);});}else{if((_Ek+_EB|0)>44){var _ER=function(_ES){while(1){var _ET=(function(_EU){var _EV=E(_EU);if(!_EV[0]){return [0];}else{var _EW=_EV[2],_EX=E(_EV[1]);if(!_EX[0]){_ES=_EW;return null;}else{var _EY=E(_EX[2]);if(!_EY[0]){_ES=_EW;return null;}else{if(!E(_EY[2])[0]){var _EZ=E(_EX[1]);if(0>(_Ek+_EZ|0)){_ES=_EW;return null;}else{if((_Ek+_EZ|0)>44){_ES=_EW;return null;}else{var _F0=E(_El),_F1=E(_EY[1]);if(0>(_F0+_F1|0)){_ES=_EW;return null;}else{if((_F0+_F1|0)>34){_ES=_EW;return null;}else{var _F2=new T(function(){return B(_ER(_EW));}),_F3=_Ek+_EZ|0,_F4=_F0+_F1|0,_F5=new T(function(){return B(_nf(_F3,_F4,_En));});return [1,[0,[0,_F3,_F4],_F5],_F2];}}}}}else{_ES=_EW;return null;}}}}})(_ES);if(_ET!=null){return _ET;}}};return new F(function(){return _ER(_Ey);});}else{var _F6=E(_El),_F7=E(_EA[1]);if(0>(_F6+_F7|0)){var _F8=function(_F9){while(1){var _Fa=(function(_Fb){var _Fc=E(_Fb);if(!_Fc[0]){return [0];}else{var _Fd=_Fc[2],_Fe=E(_Fc[1]);if(!_Fe[0]){_F9=_Fd;return null;}else{var _Ff=E(_Fe[2]);if(!_Ff[0]){_F9=_Fd;return null;}else{if(!E(_Ff[2])[0]){var _Fg=E(_Fe[1]);if(0>(_Ek+_Fg|0)){_F9=_Fd;return null;}else{if((_Ek+_Fg|0)>44){_F9=_Fd;return null;}else{var _Fh=E(_Ff[1]);if(0>(_F6+_Fh|0)){_F9=_Fd;return null;}else{if((_F6+_Fh|0)>34){_F9=_Fd;return null;}else{var _Fi=new T(function(){return B(_F8(_Fd));}),_Fj=_Ek+_Fg|0,_Fk=_F6+_Fh|0,_Fl=new T(function(){return B(_nf(_Fj,_Fk,_En));});return [1,[0,[0,_Fj,_Fk],_Fl],_Fi];}}}}}else{_F9=_Fd;return null;}}}}})(_F9);if(_Fa!=null){return _Fa;}}};return new F(function(){return _F8(_Ey);});}else{if((_F6+_F7|0)>34){var _Fm=function(_Fn){while(1){var _Fo=(function(_Fp){var _Fq=E(_Fp);if(!_Fq[0]){return [0];}else{var _Fr=_Fq[2],_Fs=E(_Fq[1]);if(!_Fs[0]){_Fn=_Fr;return null;}else{var _Ft=E(_Fs[2]);if(!_Ft[0]){_Fn=_Fr;return null;}else{if(!E(_Ft[2])[0]){var _Fu=E(_Fs[1]);if(0>(_Ek+_Fu|0)){_Fn=_Fr;return null;}else{if((_Ek+_Fu|0)>44){_Fn=_Fr;return null;}else{var _Fv=E(_Ft[1]);if(0>(_F6+_Fv|0)){_Fn=_Fr;return null;}else{if((_F6+_Fv|0)>34){_Fn=_Fr;return null;}else{var _Fw=new T(function(){return B(_Fm(_Fr));}),_Fx=_Ek+_Fu|0,_Fy=_F6+_Fv|0,_Fz=new T(function(){return B(_nf(_Fx,_Fy,_En));});return [1,[0,[0,_Fx,_Fy],_Fz],_Fw];}}}}}else{_Fn=_Fr;return null;}}}}})(_Fn);if(_Fo!=null){return _Fo;}}};return new F(function(){return _Fm(_Ey);});}else{var _FA=new T(function(){var _FB=function(_FC){while(1){var _FD=(function(_FE){var _FF=E(_FE);if(!_FF[0]){return [0];}else{var _FG=_FF[2],_FH=E(_FF[1]);if(!_FH[0]){_FC=_FG;return null;}else{var _FI=E(_FH[2]);if(!_FI[0]){_FC=_FG;return null;}else{if(!E(_FI[2])[0]){var _FJ=E(_FH[1]);if(0>(_Ek+_FJ|0)){_FC=_FG;return null;}else{if((_Ek+_FJ|0)>44){_FC=_FG;return null;}else{var _FK=E(_FI[1]);if(0>(_F6+_FK|0)){_FC=_FG;return null;}else{if((_F6+_FK|0)>34){_FC=_FG;return null;}else{var _FL=new T(function(){return B(_FB(_FG));}),_FM=_Ek+_FJ|0,_FN=_F6+_FK|0,_FO=new T(function(){return B(_nf(_FM,_FN,_En));});return [1,[0,[0,_FM,_FN],_FO],_FL];}}}}}else{_FC=_FG;return null;}}}}})(_FC);if(_FD!=null){return _FD;}}};return B(_FB(_Ey));}),_FP=_Ek+_EB|0,_FQ=_F6+_F7|0,_FR=new T(function(){return B(_nf(_FP,_FQ,_En));});return [1,[0,[0,_FP,_FQ],_FR],_FA];}}}}}else{_Eu=_Ey;return null;}}}}})(_Eu);if(_Ev!=null){return _Ev;}}};return B(_xr(_nc,B(_Et(_ye)),_Eo));}),_FS=new T(function(){var _FT=E(_El);if(0>=_FT){if(0>=_Ek){return E(_up);}else{return B(_us(_Ek));}}else{var _FU=new T(function(){var _FV=new T(function(){if(0>=_Ek){return E(_up);}else{return B(_us(_Ek));}},1);return B(_1t(_uO,_FV));}),_FW=function(_FX){var _FY=E(_FX);if(_FY==1){return E(_FU);}else{var _FZ=new T(function(){return B(_FW(_FY-1|0));},1);return new F(function(){return _1t(_uO,_FZ);});}};return B(_FW(_FT));}}),_G0=B(A(_fo,[_w,_pe,_Er[1],_fn,_FS,[0,_Ej,[0,_Ek,_El],_Em,_En,_Es,_Ep,_Eq],_])),_G1=_G0,_G2=E(_uw),_G3=jsFind(_G2);if(!_G3[0]){return new F(function(){return _ym(_G2);});}else{var _G4=new T(function(){return E(E(_G1)[2]);}),_G5=new T(function(){var _G6=new T(function(){return E(E(_G4)[5]);});return B(_vn(_G6));}),_G7=B(A(_fo,[_w,_pe,_G3[1],_fn,_G5,_G4,_])),_G8=E(E(_G7)[2]);if(E(_G8[6])==5){var _G9=E(_4k),_Ga=E(_uJ)(_G9),_Gb=E(_uH),_Gc=toJSStr(E(_yj)),_Gd=jsQuerySelectorAll(_Gb,_Gc);if(!_Gd[0]){return E(_xF);}else{if(!E(_Gd[2])[0]){var _Ge=E(_uK),_Gf=_Ge(E(_Gd[1])),_Gg=B(A(_eL,[_w,_pe,_Gf,_xC,_xB,[0,_G8[1],_G8[2],_G8[3],_G8[4],_G8[5],_uG,_G8[7]],_])),_Gh=_Gg,_Gi=E(_ux),_Gj=jsFind(_Gi);if(!_Gj[0]){return new F(function(){return _ym(_Gi);});}else{var _Gk=_Gj[1],_Gl=E(_yq),_Gm=new T(function(){return E(E(_Gh)[2]);}),_Gn=function(_){var _Go=rMV(_Gl);if(!B(_uL(B(_v9(_xz,E(E(_Go)[7])[2]))))){return _9W;}else{var _Gp=E(_uI)(_G9),_Gq=jsQuerySelectorAll(_Gb,_Gc);if(!_Gq[0]){return new F(function(){return _ud(_);});}else{if(!E(_Gq[2])[0]){var _Gr=_Ge(E(_Gq[1])),_Gs=B(A(_eL,[_w,_3a,_Gr,_xC,_yi,_])),_Gt=E(_Gk),_Gu=jsQuerySelectorAll(_Gt,toJSStr(E(_fV))),_Gv=B(_uy(_Gu,_)),_Gw=jsQuerySelectorAll(_Gt,toJSStr(E(_fU)));return new F(function(){return _uC(_Gw,_);});}else{return new F(function(){return _ud(_);});}}}};return new F(function(){return _tk(_Gk,_Gl,_Gn,_Gm,_);});}}else{return E(_xF);}}}else{return [0,_9W,_G8];}}}};if(!B(_ai(_yr,39))){return new F(function(){return _Ei(_,_Ea,_Eb,_Ec,_Ed,_Ee,_Ef,_Eg,_Eh);});}else{var _Gx=_Eb+1|0;switch(E(B(_ue(_Gx,_Ec,_Ee)))){case 35:var _Gy=new T(function(){return E(_Eg)+1|0;});return new F(function(){return _Ei(_,_Ea,_Gx,_Ec,_Ed,_Ee,_Ef,_Gy,_Eh);});break;case 45:var _Gz=new T(function(){return E(_Eg)+1|0;});return new F(function(){return _Ei(_,_Ea,_Gx,_Ec,_Ed,_Ee,_Ef,_Gz,_Eh);});break;default:return new F(function(){return _Ei(_,_Ea,_Eb,_Ec,_Ed,_Ee,_Ef,_Eg,_Eh);});}}};if(!B(_ai(_yr,37))){var _GA=function(_,_GB,_GC,_GD,_GE,_GF,_GG,_GH,_GI){var _GJ=jsFind(toJSStr(E(_yk)));if(!_GJ[0]){return new F(function(){return die(_yh);});}else{var _GK=new T(function(){var _GL=function(_GM){while(1){var _GN=(function(_GO){var _GP=E(_GO);if(!_GP[0]){return [0];}else{var _GQ=_GP[2],_GR=E(_GP[1]);if(!_GR[0]){_GM=_GQ;return null;}else{var _GS=E(_GR[2]);if(!_GS[0]){_GM=_GQ;return null;}else{if(!E(_GS[2])[0]){var _GT=E(_GR[1]);if(0>(_GC+_GT|0)){var _GU=function(_GV){while(1){var _GW=(function(_GX){var _GY=E(_GX);if(!_GY[0]){return [0];}else{var _GZ=_GY[2],_H0=E(_GY[1]);if(!_H0[0]){_GV=_GZ;return null;}else{var _H1=E(_H0[2]);if(!_H1[0]){_GV=_GZ;return null;}else{if(!E(_H1[2])[0]){var _H2=E(_H0[1]);if(0>(_GC+_H2|0)){_GV=_GZ;return null;}else{if((_GC+_H2|0)>44){_GV=_GZ;return null;}else{var _H3=E(_GD),_H4=E(_H1[1]);if(0>(_H3+_H4|0)){_GV=_GZ;return null;}else{if((_H3+_H4|0)>34){_GV=_GZ;return null;}else{var _H5=new T(function(){return B(_GU(_GZ));}),_H6=_GC+_H2|0,_H7=_H3+_H4|0,_H8=new T(function(){return B(_nf(_H6,_H7,_GF));});return [1,[0,[0,_H6,_H7],_H8],_H5];}}}}}else{_GV=_GZ;return null;}}}}})(_GV);if(_GW!=null){return _GW;}}};return new F(function(){return _GU(_GQ);});}else{if((_GC+_GT|0)>44){var _H9=function(_Ha){while(1){var _Hb=(function(_Hc){var _Hd=E(_Hc);if(!_Hd[0]){return [0];}else{var _He=_Hd[2],_Hf=E(_Hd[1]);if(!_Hf[0]){_Ha=_He;return null;}else{var _Hg=E(_Hf[2]);if(!_Hg[0]){_Ha=_He;return null;}else{if(!E(_Hg[2])[0]){var _Hh=E(_Hf[1]);if(0>(_GC+_Hh|0)){_Ha=_He;return null;}else{if((_GC+_Hh|0)>44){_Ha=_He;return null;}else{var _Hi=E(_GD),_Hj=E(_Hg[1]);if(0>(_Hi+_Hj|0)){_Ha=_He;return null;}else{if((_Hi+_Hj|0)>34){_Ha=_He;return null;}else{var _Hk=new T(function(){return B(_H9(_He));}),_Hl=_GC+_Hh|0,_Hm=_Hi+_Hj|0,_Hn=new T(function(){return B(_nf(_Hl,_Hm,_GF));});return [1,[0,[0,_Hl,_Hm],_Hn],_Hk];}}}}}else{_Ha=_He;return null;}}}}})(_Ha);if(_Hb!=null){return _Hb;}}};return new F(function(){return _H9(_GQ);});}else{var _Ho=E(_GD),_Hp=E(_GS[1]);if(0>(_Ho+_Hp|0)){var _Hq=function(_Hr){while(1){var _Hs=(function(_Ht){var _Hu=E(_Ht);if(!_Hu[0]){return [0];}else{var _Hv=_Hu[2],_Hw=E(_Hu[1]);if(!_Hw[0]){_Hr=_Hv;return null;}else{var _Hx=E(_Hw[2]);if(!_Hx[0]){_Hr=_Hv;return null;}else{if(!E(_Hx[2])[0]){var _Hy=E(_Hw[1]);if(0>(_GC+_Hy|0)){_Hr=_Hv;return null;}else{if((_GC+_Hy|0)>44){_Hr=_Hv;return null;}else{var _Hz=E(_Hx[1]);if(0>(_Ho+_Hz|0)){_Hr=_Hv;return null;}else{if((_Ho+_Hz|0)>34){_Hr=_Hv;return null;}else{var _HA=new T(function(){return B(_Hq(_Hv));}),_HB=_GC+_Hy|0,_HC=_Ho+_Hz|0,_HD=new T(function(){return B(_nf(_HB,_HC,_GF));});return [1,[0,[0,_HB,_HC],_HD],_HA];}}}}}else{_Hr=_Hv;return null;}}}}})(_Hr);if(_Hs!=null){return _Hs;}}};return new F(function(){return _Hq(_GQ);});}else{if((_Ho+_Hp|0)>34){var _HE=function(_HF){while(1){var _HG=(function(_HH){var _HI=E(_HH);if(!_HI[0]){return [0];}else{var _HJ=_HI[2],_HK=E(_HI[1]);if(!_HK[0]){_HF=_HJ;return null;}else{var _HL=E(_HK[2]);if(!_HL[0]){_HF=_HJ;return null;}else{if(!E(_HL[2])[0]){var _HM=E(_HK[1]);if(0>(_GC+_HM|0)){_HF=_HJ;return null;}else{if((_GC+_HM|0)>44){_HF=_HJ;return null;}else{var _HN=E(_HL[1]);if(0>(_Ho+_HN|0)){_HF=_HJ;return null;}else{if((_Ho+_HN|0)>34){_HF=_HJ;return null;}else{var _HO=new T(function(){return B(_HE(_HJ));}),_HP=_GC+_HM|0,_HQ=_Ho+_HN|0,_HR=new T(function(){return B(_nf(_HP,_HQ,_GF));});return [1,[0,[0,_HP,_HQ],_HR],_HO];}}}}}else{_HF=_HJ;return null;}}}}})(_HF);if(_HG!=null){return _HG;}}};return new F(function(){return _HE(_GQ);});}else{var _HS=new T(function(){var _HT=function(_HU){while(1){var _HV=(function(_HW){var _HX=E(_HW);if(!_HX[0]){return [0];}else{var _HY=_HX[2],_HZ=E(_HX[1]);if(!_HZ[0]){_HU=_HY;return null;}else{var _I0=E(_HZ[2]);if(!_I0[0]){_HU=_HY;return null;}else{if(!E(_I0[2])[0]){var _I1=E(_HZ[1]);if(0>(_GC+_I1|0)){_HU=_HY;return null;}else{if((_GC+_I1|0)>44){_HU=_HY;return null;}else{var _I2=E(_I0[1]);if(0>(_Ho+_I2|0)){_HU=_HY;return null;}else{if((_Ho+_I2|0)>34){_HU=_HY;return null;}else{var _I3=new T(function(){return B(_HT(_HY));}),_I4=_GC+_I1|0,_I5=_Ho+_I2|0,_I6=new T(function(){return B(_nf(_I4,_I5,_GF));});return [1,[0,[0,_I4,_I5],_I6],_I3];}}}}}else{_HU=_HY;return null;}}}}})(_HU);if(_HV!=null){return _HV;}}};return B(_HT(_GQ));}),_I7=_GC+_GT|0,_I8=_Ho+_Hp|0,_I9=new T(function(){return B(_nf(_I7,_I8,_GF));});return [1,[0,[0,_I7,_I8],_I9],_HS];}}}}}else{_GM=_GQ;return null;}}}}})(_GM);if(_GN!=null){return _GN;}}};return B(_xr(_nc,B(_GL(_ye)),_GG));}),_Ia=new T(function(){var _Ib=E(_GD);if(0>=_Ib){if(0>=_GC){return E(_up);}else{return B(_us(_GC));}}else{var _Ic=new T(function(){var _Id=new T(function(){if(0>=_GC){return E(_up);}else{return B(_us(_GC));}},1);return B(_1t(_uO,_Id));}),_Ie=function(_If){var _Ig=E(_If);if(_Ig==1){return E(_Ic);}else{var _Ih=new T(function(){return B(_Ie(_Ig-1|0));},1);return new F(function(){return _1t(_uO,_Ih);});}};return B(_Ie(_Ib));}}),_Ii=B(A(_fo,[_w,_pe,_GJ[1],_fn,_Ia,[0,_GB,[0,_GC,_GD],_GE,_GF,_GK,_GH,_GI],_])),_Ij=_Ii,_Ik=E(_uw),_Il=jsFind(_Ik);if(!_Il[0]){return new F(function(){return _ym(_Ik);});}else{var _Im=new T(function(){return E(E(_Ij)[2]);}),_In=new T(function(){var _Io=new T(function(){return E(E(_Im)[5]);});return B(_vn(_Io));}),_Ip=B(A(_fo,[_w,_pe,_Il[1],_fn,_In,_Im,_])),_Iq=E(E(_Ip)[2]);if(E(_Iq[6])==5){var _Ir=E(_4k),_Is=E(_uJ)(_Ir),_It=E(_uH),_Iu=toJSStr(E(_yj)),_Iv=jsQuerySelectorAll(_It,_Iu);if(!_Iv[0]){return E(_xF);}else{if(!E(_Iv[2])[0]){var _Iw=E(_uK),_Ix=_Iw(E(_Iv[1])),_Iy=B(A(_eL,[_w,_pe,_Ix,_xC,_xB,[0,_Iq[1],_Iq[2],_Iq[3],_Iq[4],_Iq[5],_uG,_Iq[7]],_])),_Iz=_Iy,_IA=E(_ux),_IB=jsFind(_IA);if(!_IB[0]){return new F(function(){return _ym(_IA);});}else{var _IC=_IB[1],_ID=E(_yq),_IE=new T(function(){return E(E(_Iz)[2]);}),_IF=function(_){var _IG=rMV(_ID);if(!B(_uL(B(_v9(_xz,E(E(_IG)[7])[2]))))){return _9W;}else{var _IH=E(_uI)(_Ir),_II=jsQuerySelectorAll(_It,_Iu);if(!_II[0]){return new F(function(){return _ud(_);});}else{if(!E(_II[2])[0]){var _IJ=_Iw(E(_II[1])),_IK=B(A(_eL,[_w,_3a,_IJ,_xC,_yi,_])),_IL=E(_IC),_IM=jsQuerySelectorAll(_IL,toJSStr(E(_fV))),_IN=B(_uy(_IM,_)),_IO=jsQuerySelectorAll(_IL,toJSStr(E(_fU)));return new F(function(){return _uC(_IO,_);});}else{return new F(function(){return _ud(_);});}}}};return new F(function(){return _tk(_IC,_ID,_IF,_IE,_);});}}else{return E(_xF);}}}else{return [0,_9W,_Iq];}}}};if(!B(_ai(_yr,39))){var _IP=jsFind(toJSStr(E(_yk)));if(!_IP[0]){return new F(function(){return die(_yh);});}else{var _IQ=new T(function(){var _IR=function(_IS){while(1){var _IT=(function(_IU){var _IV=E(_IU);if(!_IV[0]){return [0];}else{var _IW=_IV[2],_IX=E(_IV[1]);if(!_IX[0]){_IS=_IW;return null;}else{var _IY=E(_IX[2]);if(!_IY[0]){_IS=_IW;return null;}else{if(!E(_IY[2])[0]){var _IZ=E(_yy),_J0=E(_IX[1]);if(0>(_IZ+_J0|0)){var _J1=function(_J2){while(1){var _J3=(function(_J4){var _J5=E(_J4);if(!_J5[0]){return [0];}else{var _J6=_J5[2],_J7=E(_J5[1]);if(!_J7[0]){_J2=_J6;return null;}else{var _J8=E(_J7[2]);if(!_J8[0]){_J2=_J6;return null;}else{if(!E(_J8[2])[0]){var _J9=E(_J7[1]);if(0>(_IZ+_J9|0)){_J2=_J6;return null;}else{if((_IZ+_J9|0)>44){_J2=_J6;return null;}else{var _Ja=E(_yz),_Jb=E(_J8[1]);if(0>(_Ja+_Jb|0)){_J2=_J6;return null;}else{if((_Ja+_Jb|0)>34){_J2=_J6;return null;}else{var _Jc=new T(function(){return B(_J1(_J6));}),_Jd=_IZ+_J9|0,_Je=_Ja+_Jb|0,_Jf=new T(function(){return B(_nf(_Jd,_Je,_yt));});return [1,[0,[0,_Jd,_Je],_Jf],_Jc];}}}}}else{_J2=_J6;return null;}}}}})(_J2);if(_J3!=null){return _J3;}}};return new F(function(){return _J1(_IW);});}else{if((_IZ+_J0|0)>44){var _Jg=function(_Jh){while(1){var _Ji=(function(_Jj){var _Jk=E(_Jj);if(!_Jk[0]){return [0];}else{var _Jl=_Jk[2],_Jm=E(_Jk[1]);if(!_Jm[0]){_Jh=_Jl;return null;}else{var _Jn=E(_Jm[2]);if(!_Jn[0]){_Jh=_Jl;return null;}else{if(!E(_Jn[2])[0]){var _Jo=E(_Jm[1]);if(0>(_IZ+_Jo|0)){_Jh=_Jl;return null;}else{if((_IZ+_Jo|0)>44){_Jh=_Jl;return null;}else{var _Jp=E(_yz),_Jq=E(_Jn[1]);if(0>(_Jp+_Jq|0)){_Jh=_Jl;return null;}else{if((_Jp+_Jq|0)>34){_Jh=_Jl;return null;}else{var _Jr=new T(function(){return B(_Jg(_Jl));}),_Js=_IZ+_Jo|0,_Jt=_Jp+_Jq|0,_Ju=new T(function(){return B(_nf(_Js,_Jt,_yt));});return [1,[0,[0,_Js,_Jt],_Ju],_Jr];}}}}}else{_Jh=_Jl;return null;}}}}})(_Jh);if(_Ji!=null){return _Ji;}}};return new F(function(){return _Jg(_IW);});}else{var _Jv=E(_yz),_Jw=E(_IY[1]);if(0>(_Jv+_Jw|0)){var _Jx=function(_Jy){while(1){var _Jz=(function(_JA){var _JB=E(_JA);if(!_JB[0]){return [0];}else{var _JC=_JB[2],_JD=E(_JB[1]);if(!_JD[0]){_Jy=_JC;return null;}else{var _JE=E(_JD[2]);if(!_JE[0]){_Jy=_JC;return null;}else{if(!E(_JE[2])[0]){var _JF=E(_JD[1]);if(0>(_IZ+_JF|0)){_Jy=_JC;return null;}else{if((_IZ+_JF|0)>44){_Jy=_JC;return null;}else{var _JG=E(_JE[1]);if(0>(_Jv+_JG|0)){_Jy=_JC;return null;}else{if((_Jv+_JG|0)>34){_Jy=_JC;return null;}else{var _JH=new T(function(){return B(_Jx(_JC));}),_JI=_IZ+_JF|0,_JJ=_Jv+_JG|0,_JK=new T(function(){return B(_nf(_JI,_JJ,_yt));});return [1,[0,[0,_JI,_JJ],_JK],_JH];}}}}}else{_Jy=_JC;return null;}}}}})(_Jy);if(_Jz!=null){return _Jz;}}};return new F(function(){return _Jx(_IW);});}else{if((_Jv+_Jw|0)>34){var _JL=function(_JM){while(1){var _JN=(function(_JO){var _JP=E(_JO);if(!_JP[0]){return [0];}else{var _JQ=_JP[2],_JR=E(_JP[1]);if(!_JR[0]){_JM=_JQ;return null;}else{var _JS=E(_JR[2]);if(!_JS[0]){_JM=_JQ;return null;}else{if(!E(_JS[2])[0]){var _JT=E(_JR[1]);if(0>(_IZ+_JT|0)){_JM=_JQ;return null;}else{if((_IZ+_JT|0)>44){_JM=_JQ;return null;}else{var _JU=E(_JS[1]);if(0>(_Jv+_JU|0)){_JM=_JQ;return null;}else{if((_Jv+_JU|0)>34){_JM=_JQ;return null;}else{var _JV=new T(function(){return B(_JL(_JQ));}),_JW=_IZ+_JT|0,_JX=_Jv+_JU|0,_JY=new T(function(){return B(_nf(_JW,_JX,_yt));});return [1,[0,[0,_JW,_JX],_JY],_JV];}}}}}else{_JM=_JQ;return null;}}}}})(_JM);if(_JN!=null){return _JN;}}};return new F(function(){return _JL(_IW);});}else{var _JZ=new T(function(){var _K0=function(_K1){while(1){var _K2=(function(_K3){var _K4=E(_K3);if(!_K4[0]){return [0];}else{var _K5=_K4[2],_K6=E(_K4[1]);if(!_K6[0]){_K1=_K5;return null;}else{var _K7=E(_K6[2]);if(!_K7[0]){_K1=_K5;return null;}else{if(!E(_K7[2])[0]){var _K8=E(_K6[1]);if(0>(_IZ+_K8|0)){_K1=_K5;return null;}else{if((_IZ+_K8|0)>44){_K1=_K5;return null;}else{var _K9=E(_K7[1]);if(0>(_Jv+_K9|0)){_K1=_K5;return null;}else{if((_Jv+_K9|0)>34){_K1=_K5;return null;}else{var _Ka=new T(function(){return B(_K0(_K5));}),_Kb=_IZ+_K8|0,_Kc=_Jv+_K9|0,_Kd=new T(function(){return B(_nf(_Kb,_Kc,_yt));});return [1,[0,[0,_Kb,_Kc],_Kd],_Ka];}}}}}else{_K1=_K5;return null;}}}}})(_K1);if(_K2!=null){return _K2;}}};return B(_K0(_IW));}),_Ke=_IZ+_J0|0,_Kf=_Jv+_Jw|0,_Kg=new T(function(){return B(_nf(_Ke,_Kf,_yt));});return [1,[0,[0,_Ke,_Kf],_Kg],_JZ];}}}}}else{_IS=_IW;return null;}}}}})(_IS);if(_IT!=null){return _IT;}}};return B(_xr(_nc,B(_IR(_ye)),_yu));}),_Kh=new T(function(){var _Ki=E(_yz);if(0>=_Ki){var _Kj=E(_yy);if(0>=_Kj){return E(_up);}else{return B(_us(_Kj));}}else{var _Kk=new T(function(){var _Kl=new T(function(){var _Km=E(_yy);if(0>=_Km){return E(_up);}else{return B(_us(_Km));}},1);return B(_1t(_uO,_Kl));}),_Kn=function(_Ko){var _Kp=E(_Ko);if(_Kp==1){return E(_Kk);}else{var _Kq=new T(function(){return B(_Kn(_Kp-1|0));},1);return new F(function(){return _1t(_uO,_Kq);});}};return B(_Kn(_Ki));}}),_Kr=B(A(_fo,[_w,_pe,_IP[1],_fn,_Kh,[0,_yr,[0,_yy,_yz],_yx,_yt,_IQ,_yv,_yw],_])),_Ks=_Kr,_Kt=E(_uw),_Ku=jsFind(_Kt);if(!_Ku[0]){return new F(function(){return _ym(_Kt);});}else{var _Kv=new T(function(){return E(E(_Ks)[2]);}),_Kw=new T(function(){var _Kx=new T(function(){return E(E(_Kv)[5]);});return B(_vn(_Kx));}),_Ky=B(A(_fo,[_w,_pe,_Ku[1],_fn,_Kw,_Kv,_])),_Kz=E(E(_Ky)[2]);if(E(_Kz[6])==5){var _KA=E(_4k),_KB=E(_uJ)(_KA),_KC=E(_uH),_KD=toJSStr(E(_yj)),_KE=jsQuerySelectorAll(_KC,_KD);if(!_KE[0]){return E(_xF);}else{if(!E(_KE[2])[0]){var _KF=E(_uK),_KG=_KF(E(_KE[1])),_KH=B(A(_eL,[_w,_pe,_KG,_xC,_xB,[0,_Kz[1],_Kz[2],_Kz[3],_Kz[4],_Kz[5],_uG,_Kz[7]],_])),_KI=_KH,_KJ=E(_ux),_KK=jsFind(_KJ);if(!_KK[0]){return new F(function(){return _ym(_KJ);});}else{var _KL=_KK[1],_KM=E(_yq),_KN=new T(function(){return E(E(_KI)[2]);}),_KO=function(_){var _KP=rMV(_KM);if(!B(_uL(B(_v9(_xz,E(E(_KP)[7])[2]))))){return _9W;}else{var _KQ=E(_uI)(_KA),_KR=jsQuerySelectorAll(_KC,_KD);if(!_KR[0]){return new F(function(){return _ud(_);});}else{if(!E(_KR[2])[0]){var _KS=_KF(E(_KR[1])),_KT=B(A(_eL,[_w,_3a,_KS,_xC,_yi,_])),_KU=E(_KL),_KV=jsQuerySelectorAll(_KU,toJSStr(E(_fV))),_KW=B(_uy(_KV,_)),_KX=jsQuerySelectorAll(_KU,toJSStr(E(_fU)));return new F(function(){return _uC(_KX,_);});}else{return new F(function(){return _ud(_);});}}}};return new F(function(){return _tk(_KL,_KM,_KO,_KN,_);});}}else{return E(_xF);}}}else{return [0,_9W,_Kz];}}}}else{var _KY=E(_yy),_KZ=_KY+1|0;switch(E(B(_ue(_KZ,_yz,_yt)))){case 35:var _L0=new T(function(){return E(_yv)+1|0;});return new F(function(){return _GA(_,_yr,_KZ,_yz,_yx,_yt,_yu,_L0,_yw);});break;case 45:var _L1=new T(function(){return E(_yv)+1|0;});return new F(function(){return _GA(_,_yr,_KZ,_yz,_yx,_yt,_yu,_L1,_yw);});break;default:return new F(function(){return _GA(_,_yr,_KY,_yz,_yx,_yt,_yu,_yv,_yw);});}}}else{var _L2=E(_yy),_L3=_L2+(-1)|0;switch(E(B(_ue(_L3,_yz,_yt)))){case 35:var _L4=new T(function(){return E(_yv)+1|0;});return new F(function(){return _E9(_,_yr,_L3,_yz,_yx,_yt,_yu,_L4,_yw);});break;case 45:var _L5=new T(function(){return E(_yv)+1|0;});return new F(function(){return _E9(_,_yr,_L3,_yz,_yx,_yt,_yu,_L5,_yw);});break;default:return new F(function(){return _E9(_,_yr,_L2,_yz,_yx,_yt,_yu,_yv,_yw);});}}}else{var _L6=E(_yy),_L7=new T(function(){return E(_yz)+1|0;});switch(E(B(_ue(_L6,_L7,_yt)))){case 35:var _L8=new T(function(){return E(_yv)+1|0;});return new F(function(){return _Bt(_,_yr,_L6,_L7,_yx,_yt,_yu,_L8,_yw);});break;case 45:var _L9=new T(function(){return E(_yv)+1|0;});return new F(function(){return _Bt(_,_yr,_L6,_L7,_yx,_yt,_yu,_L9,_yw);});break;default:return new F(function(){return _Bt(_,_yr,_L6,_yz,_yx,_yt,_yu,_yv,_yw);});}}}else{var _La=E(_yy),_Lb=new T(function(){return E(_yz)+(-1)|0;});switch(E(B(_ue(_La,_Lb,_yt)))){case 35:var _Lc=new T(function(){return E(_yv)+1|0;});return new F(function(){return _yA(_,_yr,_La,_Lb,_yx,_yt,_yu,_Lc,_yw);});break;case 45:var _Ld=new T(function(){return E(_yv)+1|0;});return new F(function(){return _yA(_,_yr,_La,_Lb,_yx,_yt,_yu,_Ld,_yw);});break;default:return new F(function(){return _yA(_,_yr,_La,_yz,_yx,_yt,_yu,_yv,_yw);});}}},_Le=function(_Lf,_Lg,_Lh){var _Li=E(_Lh);switch(_Li[0]){case 0:var _Lj=_Li[1],_Lk=_Li[2],_Ll=_Li[3],_Lm=_Li[4],_Ln=_Lk>>>0;if(((_Lf>>>0&((_Ln-1>>>0^4294967295)>>>0^_Ln)>>>0)>>>0&4294967295)==_Lj){return ((_Lf>>>0&_Ln)>>>0==0)?[0,_Lj,_Lk,E(B(_Le(_Lf,_Lg,_Ll))),E(_Lm)]:[0,_Lj,_Lk,E(_Ll),E(B(_Le(_Lf,_Lg,_Lm)))];}else{var _Lo=(_Lf>>>0^_Lj>>>0)>>>0,_Lp=(_Lo|_Lo>>>1)>>>0,_Lq=(_Lp|_Lp>>>2)>>>0,_Lr=(_Lq|_Lq>>>4)>>>0,_Ls=(_Lr|_Lr>>>8)>>>0,_Lt=(_Ls|_Ls>>>16)>>>0,_Lu=(_Lt^_Lt>>>1)>>>0&4294967295,_Lv=_Lu>>>0;return ((_Lf>>>0&_Lv)>>>0==0)?[0,(_Lf>>>0&((_Lv-1>>>0^4294967295)>>>0^_Lv)>>>0)>>>0&4294967295,_Lu,[1,_Lf,_Lg],E(_Li)]:[0,(_Lf>>>0&((_Lv-1>>>0^4294967295)>>>0^_Lv)>>>0)>>>0&4294967295,_Lu,E(_Li),[1,_Lf,_Lg]];}break;case 1:var _Lw=_Li[1];if(_Lf!=_Lw){var _Lx=(_Lf>>>0^_Lw>>>0)>>>0,_Ly=(_Lx|_Lx>>>1)>>>0,_Lz=(_Ly|_Ly>>>2)>>>0,_LA=(_Lz|_Lz>>>4)>>>0,_LB=(_LA|_LA>>>8)>>>0,_LC=(_LB|_LB>>>16)>>>0,_LD=(_LC^_LC>>>1)>>>0&4294967295,_LE=_LD>>>0;return ((_Lf>>>0&_LE)>>>0==0)?[0,(_Lf>>>0&((_LE-1>>>0^4294967295)>>>0^_LE)>>>0)>>>0&4294967295,_LD,[1,_Lf,_Lg],E(_Li)]:[0,(_Lf>>>0&((_LE-1>>>0^4294967295)>>>0^_LE)>>>0)>>>0&4294967295,_LD,E(_Li),[1,_Lf,_Lg]];}else{return [1,_Lf,_Lg];}break;default:return [1,_Lf,_Lg];}},_LF=false,_LG=0,_LH=1,_LI=true,_LJ=function(_LK,_LL){while(1){var _LM=E(_LL);if(!_LM[0]){return [0];}else{var _LN=_LM[2],_LO=E(_LK);if(_LO==1){return E(_LN);}else{_LK=_LO-1|0;_LL=_LN;continue;}}}},_LP=function(_LQ,_LR,_LS){var _LT=E(_LQ);if(_LT==1){return E(_LS);}else{return new F(function(){return _LJ(_LT-1|0,_LS);});}},_LU=function(_LV,_LW){var _LX=E(_LW);if(!_LX[0]){return [0];}else{var _LY=_LX[1],_LZ=_LX[2],_M0=E(_LV);if(_M0==1){return [1,_LY,_17];}else{var _M1=new T(function(){return B(_LU(_M0-1|0,_LZ));});return [1,_LY,_M1];}}},_M2=function(_M3,_M4,_M5){var _M6=new T(function(){if(_M3>0){return B(_M7(_M3,B(_LP(_M3,_M4,_M5))));}else{return B(_M2(_M3,_M4,_M5));}}),_M8=new T(function(){if(0>=_M3){return [0];}else{return B(_LU(_M3,[1,_M4,_M5]));}});return [1,_M8,_M6];},_M7=function(_M9,_Ma){var _Mb=E(_Ma);if(!_Mb[0]){return [0];}else{var _Mc=_Mb[1],_Md=_Mb[2],_Me=new T(function(){if(_M9>0){return B(_M7(_M9,B(_LP(_M9,_Mc,_Md))));}else{return B(_M2(_M9,_Mc,_Md));}}),_Mf=new T(function(){if(0>=_M9){return [0];}else{return B(_LU(_M9,_Mb));}});return [1,_Mf,_Me];}},_Mg=function(_Mh,_Mi,_Mj,_Mk){var _Ml=E(_Mk);if(!_Ml[0]){var _Mm=_Ml[3],_Mn=_Ml[4],_Mo=_Ml[5],_Mp=E(_Ml[2]),_Mq=E(_Mh),_Mr=E(_Mp[1]);if(_Mq>=_Mr){if(_Mq!=_Mr){return new F(function(){return _ws(_Mp,_Mm,_Mn,B(_Mg(_Mq,_Mi,_Mj,_Mo)));});}else{var _Ms=E(_Mi),_Mt=E(_Mp[2]);if(_Ms>=_Mt){if(_Ms!=_Mt){return new F(function(){return _ws(_Mp,_Mm,_Mn,B(_Mg(_Mq,_Ms,_Mj,_Mo)));});}else{return [0,_Ml[1],[0,_Mq,_Ms],_Mj,E(_Mn),E(_Mo)];}}else{return new F(function(){return _vJ(_Mp,_Mm,B(_Mg(_Mq,_Ms,_Mj,_Mn)),_Mo);});}}}else{return new F(function(){return _vJ(_Mp,_Mm,B(_Mg(_Mq,_Mi,_Mj,_Mn)),_Mo);});}}else{return [0,1,[0,_Mh,_Mi],_Mj,E(_vE),E(_vE)];}},_Mu=function(_Mv){var _Mw=E(_Mv);if(!_Mw[0]){return [0];}else{var _Mx=_Mw[2],_My=new T(function(){return B(_Mu(_Mx));},1);return new F(function(){return _1t(_Mw[1],_My);});}},_Mz=function(_MA){return new F(function(){return _Mu(_MA);});},_MB=(function(s){return s[0];}),_MC=function(_MD,_ME){var _MF=_MD%_ME;if(_MD<=0){if(_MD>=0){return E(_MF);}else{if(_ME<=0){return E(_MF);}else{var _MG=E(_MF);return (_MG==0)?0:_MG+_ME|0;}}}else{if(_ME>=0){if(_MD>=0){return E(_MF);}else{if(_ME<=0){return E(_MF);}else{var _MH=E(_MF);return (_MH==0)?0:_MH+_ME|0;}}}else{var _MI=E(_MF);return (_MI==0)?0:_MI+_ME|0;}}},_MJ=(function(s){var ba = window['newByteArr'](16);ba['v']['w32'][0] = s[0];ba['v']['w32'][1] = s[1];ba['v']['w32'][2] = s[2];ba['v']['w32'][3] = s[3];return window['md51'](ba,16);}),_MK=function(_ML){var _MM=function(_){return new F(function(){return E(_MJ)(E(_ML));});};return new F(function(){return _4g(_MM);});},_MN=function(_MO,_MP,_MQ){while(1){var _MR=(function(_MS,_MT,_MU){if(_MS>_MT){var _MV=_MT,_MW=_MS,_MX=_MU;_MO=_MV;_MP=_MW;_MQ=_MX;return null;}else{var _MY=new T(function(){return B(_MK(_MU));}),_MZ=new T(function(){var _N0=(_MT-_MS|0)+1|0;switch(_N0){case -1:return _MS;break;case 0:return E(_ew);break;default:var _N1=function(_){var _N2=E(_MB)(E(_MU));return new F(function(){return _3R(_N2,0);});};return B(_MC(B(_4g(_N1)),_N0))+_MS|0;}});return [0,_MZ,_MY];}})(_MO,_MP,_MQ);if(_MR!=null){return _MR;}}},_N3=(function(){var ba = window['newByteArr'](16);ba['v']['f64'][0] = Math.random();ba['v']['f64'][1] = Math.random();return window['md51'](ba,16);}),_N4=function(_N5,_){while(1){var _N6=(function(_N7,_){var _N8=E(_N7);if(!_N8[0]){return _17;}else{var _N9=_N8[2],_Na=E(_N8[1]);if(!_Na[0]){_N5=_N9;return null;}else{var _Nb=_Na[2],_Nc=E(_Na[1]),_Nd=E(_Nc[1]),_Ne=E(_Nc[2]),_Nf=E(_N3),_Ng=_Nf(),_Nh=_Ng,_Ni=E(_Ne[2]),_Nj=E(_Nd[2]);if((_Ni-_Nj|0)<4){var _Nk=function(_Nl,_){var _Nm=E(_Nl);if(!_Nm[0]){return new F(function(){return _N4(_N9,_);});}else{var _Nn=_Nm[2],_No=E(_Nm[1]),_Np=E(_No[1]),_Nq=E(_No[2]),_Nr=_Nf(),_Ns=_Nr,_Nt=E(_Nq[2]),_Nu=E(_Np[2]);if((_Nt-_Nu|0)<4){var _Nv=B(_Nk(_Nn,_));return [1,_17,_Nv];}else{var _Nw=B(_Nk(_Nn,_)),_Nx=new T(function(){return E(B(_MN((_Nu+2|0)+1|0,(_Nt-2|0)-1|0,_Ns))[1]);});return [1,[1,[0,_Np,[0,_Nq[1],_Nx]],[1,[0,[0,_Np[1],_Nx],_Nq],_17]],_Nw];}}},_Ny=B(_Nk(_Nb,_));return [1,_17,_Ny];}else{var _Nz=function(_NA,_){var _NB=E(_NA);if(!_NB[0]){return new F(function(){return _N4(_N9,_);});}else{var _NC=_NB[2],_ND=E(_NB[1]),_NE=E(_ND[1]),_NF=E(_ND[2]),_NG=_Nf(),_NH=_NG,_NI=E(_NF[2]),_NJ=E(_NE[2]);if((_NI-_NJ|0)<4){var _NK=B(_Nz(_NC,_));return [1,_17,_NK];}else{var _NL=B(_Nz(_NC,_)),_NM=new T(function(){return E(B(_MN((_NJ+2|0)+1|0,(_NI-2|0)-1|0,_NH))[1]);});return [1,[1,[0,_NE,[0,_NF[1],_NM]],[1,[0,[0,_NE[1],_NM],_NF],_17]],_NL];}}},_NN=B(_Nz(_Nb,_)),_NO=new T(function(){return E(B(_MN((_Nj+2|0)+1|0,(_Ni-2|0)-1|0,_Nh))[1]);});return [1,[1,[0,_Nd,[0,_Ne[1],_NO]],[1,[0,[0,_Nd[1],_NO],_Ne],_17]],_NN];}}}})(_N5,_);if(_N6!=null){return _N6;}}},_NP=function(_NQ,_){var _NR=E(_NQ);if(!_NR[0]){return _17;}else{var _NS=_NR[2],_NT=E(_NR[1]),_NU=E(_NT[1]),_NV=E(_NT[2]),_NW=E(_N3),_NX=_NW(),_NY=_NX,_NZ=E(_NV[1]),_O0=E(_NU[1]);if((_NZ-_O0|0)<4){var _O1=function(_O2,_){var _O3=E(_O2);if(!_O3[0]){return _17;}else{var _O4=_O3[2],_O5=E(_O3[1]),_O6=E(_O5[1]),_O7=E(_O5[2]),_O8=_NW(),_O9=_O8,_Oa=E(_O7[1]),_Ob=E(_O6[1]);if((_Oa-_Ob|0)<4){var _Oc=B(_O1(_O4,_));return [1,_17,_Oc];}else{var _Od=B(_O1(_O4,_)),_Oe=new T(function(){return E(B(_MN((_Ob+2|0)+1|0,(_Oa-2|0)-1|0,_O9))[1]);});return [1,[1,[0,_O6,[0,_Oe,_O7[2]]],[1,[0,[0,_Oe,_O6[2]],_O7],_17]],_Od];}}},_Of=B(_O1(_NS,_));return [1,_17,_Of];}else{var _Og=function(_Oh,_){var _Oi=E(_Oh);if(!_Oi[0]){return _17;}else{var _Oj=_Oi[2],_Ok=E(_Oi[1]),_Ol=E(_Ok[1]),_Om=E(_Ok[2]),_On=_NW(),_Oo=_On,_Op=E(_Om[1]),_Oq=E(_Ol[1]);if((_Op-_Oq|0)<4){var _Or=B(_Og(_Oj,_));return [1,_17,_Or];}else{var _Os=B(_Og(_Oj,_)),_Ot=new T(function(){return E(B(_MN((_Oq+2|0)+1|0,(_Op-2|0)-1|0,_Oo))[1]);});return [1,[1,[0,_Ol,[0,_Ot,_Om[2]]],[1,[0,[0,_Ot,_Ol[2]],_Om],_17]],_Os];}}},_Ou=B(_Og(_NS,_)),_Ov=new T(function(){return E(B(_MN((_O0+2|0)+1|0,(_NZ-2|0)-1|0,_NY))[1]);});return [1,[1,[0,_NU,[0,_Ov,_NV[2]]],[1,[0,[0,_Ov,_NU[2]],_NV],_17]],_Ou];}}},_Ow=0,_Ox=[0,_Ow,_Ow],_Oy=34,_Oz=44,_OA=[0,_Oz,_Oy],_OB=[0,_Ox,_OA],_OC=[1,_OB,_17],_OD=function(_OE,_){var _OF=E(_OE);if(_OF==1){var _OG=B(_NP(_OC,_)),_OH=B(_N4(_OG,_)),_OI=_OH;return new T(function(){return B(_Mz(_OI));});}else{var _OJ=B(_OD(_OF+1|0,_)),_OK=B(_NP(_OJ,_)),_OL=B(_N4(_OK,_)),_OM=_OL;return new T(function(){return B(_Mz(_OM));});}},_ON=function(_OO,_){var _OP=E(_OO);if(!_OP[0]){return _17;}else{var _OQ=_OP[2],_OR=E(_OP[1]),_OS=E(_OR[1]),_OT=E(_OR[2]),_OU=E(_N3),_OV=_OU(),_OW=_OV,_OX=_OU(),_OY=_OX,_OZ=_OU(),_P0=_OZ,_P1=_OU(),_P2=_P1,_P3=E(_OS[1]),_P4=E(_OT[1]);if((_P3+1|0)>(_P4-2|0)){var _P5=function(_P6,_){while(1){var _P7=(function(_P8,_){var _P9=E(_P8);if(!_P9[0]){return _17;}else{var _Pa=_P9[2],_Pb=E(_P9[1]),_Pc=E(_Pb[1]),_Pd=E(_Pb[2]),_Pe=_OU(),_Pf=_Pe,_Pg=_OU(),_Ph=_Pg,_Pi=_OU(),_Pj=_Pi,_Pk=_OU(),_Pl=_Pk,_Pm=E(_Pc[1]),_Pn=E(_Pd[1]);if((_Pm+1|0)>(_Pn-2|0)){_P6=_Pa;return null;}else{var _Po=E(_Pc[2]),_Pp=E(_Pd[2]);if((_Po+1|0)>(_Pp-2|0)){_P6=_Pa;return null;}else{var _Pq=B(_P5(_Pa,_)),_Pr=new T(function(){return E(B(_MN(_Pm+1|0,_Pn-2|0,_Pf))[1]);}),_Ps=new T(function(){return E(B(_MN(_Po+1|0,_Pp-2|0,_Pj))[1]);}),_Pt=new T(function(){return E(B(_MN((E(_Ps)+2|0)-1|0,_Pp-1|0,_Pl))[1]);}),_Pu=new T(function(){return E(B(_MN((E(_Pr)+2|0)-1|0,_Pn-1|0,_Ph))[1]);});return [1,[0,[0,_Pr,_Ps],[0,_Pu,_Pt]],_Pq];}}}})(_P6,_);if(_P7!=null){return _P7;}}};return new F(function(){return _P5(_OQ,_);});}else{var _Pv=E(_OS[2]),_Pw=E(_OT[2]);if((_Pv+1|0)>(_Pw-2|0)){var _Px=function(_Py,_){while(1){var _Pz=(function(_PA,_){var _PB=E(_PA);if(!_PB[0]){return _17;}else{var _PC=_PB[2],_PD=E(_PB[1]),_PE=E(_PD[1]),_PF=E(_PD[2]),_PG=_OU(),_PH=_PG,_PI=_OU(),_PJ=_PI,_PK=_OU(),_PL=_PK,_PM=_OU(),_PN=_PM,_PO=E(_PE[1]),_PP=E(_PF[1]);if((_PO+1|0)>(_PP-2|0)){_Py=_PC;return null;}else{var _PQ=E(_PE[2]),_PR=E(_PF[2]);if((_PQ+1|0)>(_PR-2|0)){_Py=_PC;return null;}else{var _PS=B(_Px(_PC,_)),_PT=new T(function(){return E(B(_MN(_PO+1|0,_PP-2|0,_PH))[1]);}),_PU=new T(function(){return E(B(_MN(_PQ+1|0,_PR-2|0,_PL))[1]);}),_PV=new T(function(){return E(B(_MN((E(_PU)+2|0)-1|0,_PR-1|0,_PN))[1]);}),_PW=new T(function(){return E(B(_MN((E(_PT)+2|0)-1|0,_PP-1|0,_PJ))[1]);});return [1,[0,[0,_PT,_PU],[0,_PW,_PV]],_PS];}}}})(_Py,_);if(_Pz!=null){return _Pz;}}};return new F(function(){return _Px(_OQ,_);});}else{var _PX=function(_PY,_){while(1){var _PZ=(function(_Q0,_){var _Q1=E(_Q0);if(!_Q1[0]){return _17;}else{var _Q2=_Q1[2],_Q3=E(_Q1[1]),_Q4=E(_Q3[1]),_Q5=E(_Q3[2]),_Q6=_OU(),_Q7=_Q6,_Q8=_OU(),_Q9=_Q8,_Qa=_OU(),_Qb=_Qa,_Qc=_OU(),_Qd=_Qc,_Qe=E(_Q4[1]),_Qf=E(_Q5[1]);if((_Qe+1|0)>(_Qf-2|0)){_PY=_Q2;return null;}else{var _Qg=E(_Q4[2]),_Qh=E(_Q5[2]);if((_Qg+1|0)>(_Qh-2|0)){_PY=_Q2;return null;}else{var _Qi=B(_PX(_Q2,_)),_Qj=new T(function(){return E(B(_MN(_Qe+1|0,_Qf-2|0,_Q7))[1]);}),_Qk=new T(function(){return E(B(_MN(_Qg+1|0,_Qh-2|0,_Qb))[1]);}),_Ql=new T(function(){return E(B(_MN((E(_Qk)+2|0)-1|0,_Qh-1|0,_Qd))[1]);}),_Qm=new T(function(){return E(B(_MN((E(_Qj)+2|0)-1|0,_Qf-1|0,_Q9))[1]);});return [1,[0,[0,_Qj,_Qk],[0,_Qm,_Ql]],_Qi];}}}})(_PY,_);if(_PZ!=null){return _PZ;}}},_Qn=B(_PX(_OQ,_)),_Qo=new T(function(){return E(B(_MN(_P3+1|0,_P4-2|0,_OW))[1]);}),_Qp=new T(function(){return E(B(_MN(_Pv+1|0,_Pw-2|0,_P0))[1]);}),_Qq=new T(function(){return E(B(_MN((E(_Qp)+2|0)-1|0,_Pw-1|0,_P2))[1]);}),_Qr=new T(function(){return E(B(_MN((E(_Qo)+2|0)-1|0,_P4-1|0,_OY))[1]);});return [1,[0,[0,_Qo,_Qp],[0,_Qr,_Qq]],_Qn];}}}},_Qs=function(_Qt,_Qu,_){var _Qv=E(_Qt);if(!_Qv[0]){return _17;}else{var _Qw=_Qv[2],_Qx=E(_Qu);if(!_Qx[0]){return _17;}else{var _Qy=_Qx[2],_Qz=E(_Qv[1]),_QA=E(_Qz[2]),_QB=E(_Qx[1]),_QC=E(_QB[1]),_QD=_QC[1],_QE=E(_QB[2])[1],_QF=E(E(_Qz[1])[2]);if(!E(_QF)){var _QG=B(_Qs(_Qw,_Qy,_));return [1,_17,_QG];}else{var _QH=E(_N3),_QI=_QH(),_QJ=_QI,_QK=function(_QL,_QM,_){var _QN=E(_QL);if(!_QN[0]){return _17;}else{var _QO=_QN[2],_QP=E(_QM);if(!_QP[0]){return _17;}else{var _QQ=_QP[2],_QR=E(_QN[1]),_QS=E(_QR[2]),_QT=E(_QP[1]),_QU=E(_QT[1]),_QV=_QU[1],_QW=E(_QT[2])[1],_QX=E(E(_QR[1])[2]);if(!E(_QX)){var _QY=B(_QK(_QO,_QQ,_));return [1,_17,_QY];}else{var _QZ=_QH(),_R0=_QZ,_R1=B(_QK(_QO,_QQ,_)),_R2=new T(function(){return E(B(_MN(E(_QV),E(_QW),_R0))[1]);});return [1,[1,[0,[0,[0,_R2,_QX],[0,_R2,_QU[2]]],[0,_R2,_QX]],_17],_R1];}}}},_R3=B(_QK(_Qw,_Qy,_)),_R4=new T(function(){return E(B(_MN(E(_QD),E(_QE),_QJ))[1]);});return [1,[1,[0,[0,[0,_R4,_QF],[0,_R4,_QC[2]]],[0,_R4,_QF]],_17],_R3];}}}},_R5=function(_R6,_R7,_){var _R8=E(_R6);if(!_R8[0]){return _17;}else{var _R9=_R8[2],_Ra=E(_R7);if(!_Ra[0]){return _17;}else{var _Rb=_Ra[2],_Rc=E(_R8[1]),_Rd=E(_Rc[1]),_Re=E(_Ra[1]),_Rf=E(_Re[1])[1],_Rg=E(_Re[2]),_Rh=_Rg[1],_Ri=E(E(_Rc[2])[2]);if(E(_Ri)==34){var _Rj=B(_R5(_R9,_Rb,_));return [1,_17,_Rj];}else{var _Rk=E(_N3),_Rl=_Rk(),_Rm=_Rl,_Rn=function(_Ro,_Rp,_){var _Rq=E(_Ro);if(!_Rq[0]){return _17;}else{var _Rr=_Rq[2],_Rs=E(_Rp);if(!_Rs[0]){return _17;}else{var _Rt=_Rs[2],_Ru=E(_Rq[1]),_Rv=E(_Ru[1]),_Rw=E(_Rs[1]),_Rx=E(_Rw[1])[1],_Ry=E(_Rw[2]),_Rz=_Ry[1],_RA=E(E(_Ru[2])[2]);if(E(_RA)==34){var _RB=B(_Rn(_Rr,_Rt,_));return [1,_17,_RB];}else{var _RC=_Rk(),_RD=_RC,_RE=B(_Rn(_Rr,_Rt,_)),_RF=new T(function(){return E(B(_MN(E(_Rx),E(_Rz),_RD))[1]);});return [1,[1,[0,[0,[0,_RF,_Ry[2]],[0,_RF,_RA]],[0,_RF,_RA]],_17],_RE];}}}},_RG=B(_Rn(_R9,_Rb,_)),_RH=new T(function(){return E(B(_MN(E(_Rf),E(_Rh),_Rm))[1]);});return [1,[1,[0,[0,[0,_RH,_Rg[2]],[0,_RH,_Ri]],[0,_RH,_Ri]],_17],_RG];}}}},_RI=function(_RJ,_RK,_){var _RL=E(_RJ);if(!_RL[0]){return _17;}else{var _RM=_RL[2],_RN=E(_RK);if(!_RN[0]){return _17;}else{var _RO=_RN[2],_RP=E(_RL[1]),_RQ=E(_RP[2]),_RR=E(_RN[1]),_RS=E(_RR[1]),_RT=_RS[2],_RU=E(_RR[2])[2],_RV=E(E(_RP[1])[1]);if(!E(_RV)){var _RW=B(_RI(_RM,_RO,_));return [1,_17,_RW];}else{var _RX=E(_N3),_RY=_RX(),_RZ=_RY,_S0=function(_S1,_S2,_){var _S3=E(_S1);if(!_S3[0]){return _17;}else{var _S4=_S3[2],_S5=E(_S2);if(!_S5[0]){return _17;}else{var _S6=_S5[2],_S7=E(_S3[1]),_S8=E(_S7[2]),_S9=E(_S5[1]),_Sa=E(_S9[1]),_Sb=_Sa[2],_Sc=E(_S9[2])[2],_Sd=E(E(_S7[1])[1]);if(!E(_Sd)){var _Se=B(_S0(_S4,_S6,_));return [1,_17,_Se];}else{var _Sf=_RX(),_Sg=_Sf,_Sh=B(_S0(_S4,_S6,_)),_Si=new T(function(){return E(B(_MN(E(_Sb),E(_Sc),_Sg))[1]);});return [1,[1,[0,[0,[0,_Sd,_Si],[0,_Sa[1],_Si]],[0,_Sd,_Si]],_17],_Sh];}}}},_Sj=B(_S0(_RM,_RO,_)),_Sk=new T(function(){return E(B(_MN(E(_RT),E(_RU),_RZ))[1]);});return [1,[1,[0,[0,[0,_RV,_Sk],[0,_RS[1],_Sk]],[0,_RV,_Sk]],_17],_Sj];}}}},_Sl=function(_Sm,_Sn,_){var _So=E(_Sm);if(!_So[0]){return _17;}else{var _Sp=_So[2],_Sq=E(_Sn);if(!_Sq[0]){return _17;}else{var _Sr=_Sq[2],_Ss=E(_So[1]),_St=E(_Ss[1]),_Su=E(_Sq[1]),_Sv=E(_Su[1])[2],_Sw=E(_Su[2]),_Sx=_Sw[2],_Sy=E(E(_Ss[2])[1]);if(E(_Sy)==44){var _Sz=B(_Sl(_Sp,_Sr,_));return [1,_17,_Sz];}else{var _SA=E(_N3),_SB=_SA(),_SC=_SB,_SD=function(_SE,_SF,_){var _SG=E(_SE);if(!_SG[0]){return _17;}else{var _SH=_SG[2],_SI=E(_SF);if(!_SI[0]){return _17;}else{var _SJ=_SI[2],_SK=E(_SG[1]),_SL=E(_SK[1]),_SM=E(_SI[1]),_SN=E(_SM[1])[2],_SO=E(_SM[2]),_SP=_SO[2],_SQ=E(E(_SK[2])[1]);if(E(_SQ)==44){var _SR=B(_SD(_SH,_SJ,_));return [1,_17,_SR];}else{var _SS=_SA(),_ST=_SS,_SU=B(_SD(_SH,_SJ,_)),_SV=new T(function(){return E(B(_MN(E(_SN),E(_SP),_ST))[1]);});return [1,[1,[0,[0,[0,_SO[1],_SV],[0,_SQ,_SV]],[0,_SQ,_SV]],_17],_SU];}}}},_SW=B(_SD(_Sp,_Sr,_)),_SX=new T(function(){return E(B(_MN(E(_Sv),E(_Sx),_SC))[1]);});return [1,[1,[0,[0,[0,_Sw[1],_SX],[0,_Sy,_SX]],[0,_Sy,_SX]],_17],_SW];}}}},_SY=function(_SZ,_T0){return [0,1,E(_SZ),_T0,E(_vE),E(_vE)];},_T1=function(_T2,_T3,_T4){var _T5=E(_T4);if(!_T5[0]){return new F(function(){return _ws(_T5[2],_T5[3],_T5[4],B(_T1(_T2,_T3,_T5[5])));});}else{return new F(function(){return _SY(_T2,_T3);});}},_T6=function(_T7,_T8,_T9){var _Ta=E(_T9);if(!_Ta[0]){return new F(function(){return _vJ(_Ta[2],_Ta[3],B(_T6(_T7,_T8,_Ta[4])),_Ta[5]);});}else{return new F(function(){return _SY(_T7,_T8);});}},_Tb=function(_Tc,_Td,_Te,_Tf,_Tg,_Th,_Ti){return new F(function(){return _vJ(_Tf,_Tg,B(_T6(_Tc,_Td,_Th)),_Ti);});},_Tj=function(_Tk,_Tl,_Tm,_Tn,_To,_Tp,_Tq,_Tr){var _Ts=E(_Tm);if(!_Ts[0]){var _Tt=_Ts[1],_Tu=_Ts[2],_Tv=_Ts[3],_Tw=_Ts[4],_Tx=_Ts[5];if((imul(3,_Tt)|0)>=_Tn){if((imul(3,_Tn)|0)>=_Tt){return [0,(_Tt+_Tn|0)+1|0,E(_Tk),_Tl,E(_Ts),[0,_Tn,E(_To),_Tp,E(_Tq),E(_Tr)]];}else{return new F(function(){return _ws(_Tu,_Tv,_Tw,B(_Tj(_Tk,_Tl,_Tx,_Tn,_To,_Tp,_Tq,_Tr)));});}}else{return new F(function(){return _vJ(_To,_Tp,B(_Ty(_Tk,_Tl,_Tt,_Tu,_Tv,_Tw,_Tx,_Tq)),_Tr);});}}else{return new F(function(){return _Tb(_Tk,_Tl,_Tn,_To,_Tp,_Tq,_Tr);});}},_Ty=function(_Tz,_TA,_TB,_TC,_TD,_TE,_TF,_TG){var _TH=E(_TG);if(!_TH[0]){var _TI=_TH[1],_TJ=_TH[2],_TK=_TH[3],_TL=_TH[4],_TM=_TH[5];if((imul(3,_TB)|0)>=_TI){if((imul(3,_TI)|0)>=_TB){return [0,(_TB+_TI|0)+1|0,E(_Tz),_TA,[0,_TB,E(_TC),_TD,E(_TE),E(_TF)],E(_TH)];}else{return new F(function(){return _ws(_TC,_TD,_TE,B(_Tj(_Tz,_TA,_TF,_TI,_TJ,_TK,_TL,_TM)));});}}else{return new F(function(){return _vJ(_TJ,_TK,B(_Ty(_Tz,_TA,_TB,_TC,_TD,_TE,_TF,_TL)),_TM);});}}else{return new F(function(){return _T1(_Tz,_TA,[0,_TB,E(_TC),_TD,E(_TE),E(_TF)]);});}},_TN=function(_TO,_TP,_TQ,_TR){var _TS=E(_TQ);if(!_TS[0]){var _TT=_TS[1],_TU=_TS[2],_TV=_TS[3],_TW=_TS[4],_TX=_TS[5],_TY=E(_TR);if(!_TY[0]){var _TZ=_TY[1],_U0=_TY[2],_U1=_TY[3],_U2=_TY[4],_U3=_TY[5];if((imul(3,_TT)|0)>=_TZ){if((imul(3,_TZ)|0)>=_TT){return [0,(_TT+_TZ|0)+1|0,E(_TO),_TP,E(_TS),E(_TY)];}else{return new F(function(){return _ws(_TU,_TV,_TW,B(_Tj(_TO,_TP,_TX,_TZ,_U0,_U1,_U2,_U3)));});}}else{return new F(function(){return _vJ(_U0,_U1,B(_Ty(_TO,_TP,_TT,_TU,_TV,_TW,_TX,_U2)),_U3);});}}else{return new F(function(){return _T1(_TO,_TP,_TS);});}}else{return new F(function(){return _T6(_TO,_TP,_TR);});}},_U4=function(_U5,_U6,_U7,_U8,_U9){var _Ua=E(_U5);if(_Ua==1){var _Ub=E(_U9);if(!_Ub[0]){return [0,[0,1,[0,_U6,_U7],_U8,E(_vE),E(_vE)],_17,_17];}else{var _Uc=E(E(_Ub[1])[1]),_Ud=E(_Uc[1]);return (_U6>=_Ud)?(_U6!=_Ud)?[0,[0,1,[0,_U6,_U7],_U8,E(_vE),E(_vE)],_17,_Ub]:(_U7<E(_Uc[2]))?[0,[0,1,[0,_U6,_U7],_U8,E(_vE),E(_vE)],_Ub,_17]:[0,[0,1,[0,_U6,_U7],_U8,E(_vE),E(_vE)],_17,_Ub]:[0,[0,1,[0,_U6,_U7],_U8,E(_vE),E(_vE)],_Ub,_17];}}else{var _Ue=B(_U4(_Ua>>1,_U6,_U7,_U8,_U9)),_Uf=_Ue[1],_Ug=_Ue[3],_Uh=E(_Ue[2]);if(!_Uh[0]){return [0,_Uf,_17,_Ug];}else{var _Ui=E(_Uh[1]),_Uj=_Ui[1],_Uk=_Ui[2],_Ul=E(_Uh[2]);if(!_Ul[0]){var _Um=new T(function(){return B(_T1(_Uj,_Uk,_Uf));});return [0,_Um,_17,_Ug];}else{var _Un=_Ul[2],_Uo=E(_Ul[1]),_Up=_Uo[2],_Uq=E(_Uj),_Ur=E(_Uo[1]),_Us=_Ur[2],_Ut=E(_Uq[1]),_Uu=E(_Ur[1]);if(_Ut>=_Uu){if(_Ut!=_Uu){return [0,_Uf,_17,_Uh];}else{var _Uv=E(_Us);if(E(_Uq[2])<_Uv){var _Uw=B(_U4(_Ua>>1,_Uu,_Uv,_Up,_Un)),_Ux=_Uw[1],_Uy=new T(function(){return B(_TN(_Uq,_Uk,_Uf,_Ux));});return [0,_Uy,_Uw[2],_Uw[3]];}else{return [0,_Uf,_17,_Uh];}}}else{var _Uz=B(_UA(_Ua>>1,_Uu,_Us,_Up,_Un)),_UB=_Uz[1],_UC=new T(function(){return B(_TN(_Uq,_Uk,_Uf,_UB));});return [0,_UC,_Uz[2],_Uz[3]];}}}}},_UA=function(_UD,_UE,_UF,_UG,_UH){var _UI=E(_UD);if(_UI==1){var _UJ=E(_UH);if(!_UJ[0]){return [0,[0,1,[0,_UE,_UF],_UG,E(_vE),E(_vE)],_17,_17];}else{var _UK=E(E(_UJ[1])[1]),_UL=E(_UK[1]);if(_UE>=_UL){if(_UE!=_UL){return [0,[0,1,[0,_UE,_UF],_UG,E(_vE),E(_vE)],_17,_UJ];}else{var _UM=E(_UF);return (_UM<E(_UK[2]))?[0,[0,1,[0,_UE,_UM],_UG,E(_vE),E(_vE)],_UJ,_17]:[0,[0,1,[0,_UE,_UM],_UG,E(_vE),E(_vE)],_17,_UJ];}}else{return [0,[0,1,[0,_UE,_UF],_UG,E(_vE),E(_vE)],_UJ,_17];}}}else{var _UN=B(_UA(_UI>>1,_UE,_UF,_UG,_UH)),_UO=_UN[1],_UP=_UN[3],_UQ=E(_UN[2]);if(!_UQ[0]){return [0,_UO,_17,_UP];}else{var _UR=E(_UQ[1]),_US=_UR[1],_UT=_UR[2],_UU=E(_UQ[2]);if(!_UU[0]){var _UV=new T(function(){return B(_T1(_US,_UT,_UO));});return [0,_UV,_17,_UP];}else{var _UW=_UU[2],_UX=E(_UU[1]),_UY=_UX[2],_UZ=E(_US),_V0=E(_UX[1]),_V1=_V0[2],_V2=E(_UZ[1]),_V3=E(_V0[1]);if(_V2>=_V3){if(_V2!=_V3){return [0,_UO,_17,_UQ];}else{var _V4=E(_V1);if(E(_UZ[2])<_V4){var _V5=B(_U4(_UI>>1,_V3,_V4,_UY,_UW)),_V6=_V5[1],_V7=new T(function(){return B(_TN(_UZ,_UT,_UO,_V6));});return [0,_V7,_V5[2],_V5[3]];}else{return [0,_UO,_17,_UQ];}}}else{var _V8=B(_UA(_UI>>1,_V3,_V1,_UY,_UW)),_V9=_V8[1],_Va=new T(function(){return B(_TN(_UZ,_UT,_UO,_V9));});return [0,_Va,_V8[2],_V8[3]];}}}}},_Vb=function(_Vc,_Vd){while(1){var _Ve=E(_Vd);if(!_Ve[0]){return E(_Vc);}else{var _Vf=E(_Ve[1]),_Vg=E(_Vf[1]),_Vh=B(_Mg(_Vg[1],_Vg[2],_Vf[2],_Vc));_Vd=_Ve[2];_Vc=_Vh;continue;}}},_Vi=function(_Vj,_Vk,_Vl,_Vm,_Vn){return new F(function(){return _Vb(B(_Mg(_Vk,_Vl,_Vm,_Vj)),_Vn);});},_Vo=function(_Vp,_Vq,_Vr){var _Vs=E(_Vq),_Vt=E(_Vs[1]);return new F(function(){return _Vb(B(_Mg(_Vt[1],_Vt[2],_Vs[2],_Vp)),_Vr);});},_Vu=function(_Vv,_Vw,_Vx){var _Vy=E(_Vx);if(!_Vy[0]){return E(_Vw);}else{var _Vz=E(_Vy[1]),_VA=_Vz[1],_VB=_Vz[2],_VC=E(_Vy[2]);if(!_VC[0]){return new F(function(){return _T1(_VA,_VB,_Vw);});}else{var _VD=_VC[2],_VE=E(_VC[1]),_VF=_VE[2],_VG=E(_VA),_VH=_VG[2],_VI=E(_VE[1]),_VJ=_VI[2],_VK=E(_VG[1]),_VL=E(_VI[1]),_VM=function(_VN){var _VO=B(_UA(_Vv,_VL,_VJ,_VF,_VD)),_VP=_VO[1],_VQ=E(_VO[3]);if(!_VQ[0]){return new F(function(){return _Vu(_Vv<<1,B(_TN(_VG,_VB,_Vw,_VP)),_VO[2]);});}else{return new F(function(){return _Vo(B(_TN(_VG,_VB,_Vw,_VP)),_VQ[1],_VQ[2]);});}};if(_VK>=_VL){if(_VK!=_VL){return new F(function(){return _Vi(_Vw,_VK,_VH,_VB,_VC);});}else{var _VR=E(_VH);if(_VR<E(_VJ)){return new F(function(){return _VM(_);});}else{return new F(function(){return _Vi(_Vw,_VK,_VR,_VB,_VC);});}}}else{return new F(function(){return _VM(_);});}}}},_VS=function(_VT,_VU,_VV,_VW,_VX,_VY){var _VZ=E(_VY);if(!_VZ[0]){return new F(function(){return _T1([0,_VV,_VW],_VX,_VU);});}else{var _W0=_VZ[2],_W1=E(_VZ[1]),_W2=_W1[2],_W3=E(_W1[1]),_W4=_W3[2],_W5=E(_W3[1]),_W6=function(_W7){var _W8=B(_UA(_VT,_W5,_W4,_W2,_W0)),_W9=_W8[1],_Wa=E(_W8[3]);if(!_Wa[0]){return new F(function(){return _Vu(_VT<<1,B(_TN([0,_VV,_VW],_VX,_VU,_W9)),_W8[2]);});}else{return new F(function(){return _Vo(B(_TN([0,_VV,_VW],_VX,_VU,_W9)),_Wa[1],_Wa[2]);});}};if(_VV>=_W5){if(_VV!=_W5){return new F(function(){return _Vi(_VU,_VV,_VW,_VX,_VZ);});}else{if(_VW<E(_W4)){return new F(function(){return _W6(_);});}else{return new F(function(){return _Vi(_VU,_VV,_VW,_VX,_VZ);});}}}else{return new F(function(){return _W6(_);});}}},_Wb=function(_Wc,_Wd,_We,_Wf,_Wg,_Wh){var _Wi=E(_Wh);if(!_Wi[0]){return new F(function(){return _T1([0,_We,_Wf],_Wg,_Wd);});}else{var _Wj=_Wi[2],_Wk=E(_Wi[1]),_Wl=_Wk[2],_Wm=E(_Wk[1]),_Wn=_Wm[2],_Wo=E(_Wm[1]),_Wp=function(_Wq){var _Wr=B(_UA(_Wc,_Wo,_Wn,_Wl,_Wj)),_Ws=_Wr[1],_Wt=E(_Wr[3]);if(!_Wt[0]){return new F(function(){return _Vu(_Wc<<1,B(_TN([0,_We,_Wf],_Wg,_Wd,_Ws)),_Wr[2]);});}else{return new F(function(){return _Vo(B(_TN([0,_We,_Wf],_Wg,_Wd,_Ws)),_Wt[1],_Wt[2]);});}};if(_We>=_Wo){if(_We!=_Wo){return new F(function(){return _Vi(_Wd,_We,_Wf,_Wg,_Wi);});}else{var _Wu=E(_Wf);if(_Wu<E(_Wn)){return new F(function(){return _Wp(_);});}else{return new F(function(){return _Vi(_Wd,_We,_Wu,_Wg,_Wi);});}}}else{return new F(function(){return _Wp(_);});}}},_Wv=function(_Ww){var _Wx=E(_Ww);if(!_Wx[0]){return [1];}else{var _Wy=E(_Wx[1]),_Wz=_Wy[1],_WA=_Wy[2],_WB=E(_Wx[2]);if(!_WB[0]){return [0,1,E(_Wz),_WA,E(_vE),E(_vE)];}else{var _WC=_WB[2],_WD=E(_WB[1]),_WE=_WD[2],_WF=E(_Wz),_WG=E(_WD[1]),_WH=_WG[2],_WI=E(_WF[1]),_WJ=E(_WG[1]);if(_WI>=_WJ){if(_WI!=_WJ){return new F(function(){return _Vi([0,1,E(_WF),_WA,E(_vE),E(_vE)],_WJ,_WH,_WE,_WC);});}else{var _WK=E(_WH);if(E(_WF[2])<_WK){return new F(function(){return _VS(1,[0,1,E(_WF),_WA,E(_vE),E(_vE)],_WJ,_WK,_WE,_WC);});}else{return new F(function(){return _Vi([0,1,E(_WF),_WA,E(_vE),E(_vE)],_WJ,_WK,_WE,_WC);});}}}else{return new F(function(){return _Wb(1,[0,1,E(_WF),_WA,E(_vE),E(_vE)],_WJ,_WH,_WE,_WC);});}}}},_WL=new T(function(){return B(_uP(0,34));}),_WM=function(_WN){var _WO=_WN,_WP=new T(function(){var _WQ=E(_WN);if(_WQ==44){return [0];}else{return B(_WM(_WQ+1|0));}}),_WR=function(_WS){var _WT=E(_WS);if(!_WT[0]){return E(_WP);}else{var _WU=_WT[2],_WV=new T(function(){return B(_WR(_WU));});return [1,[0,_WO,_WT[1]],_WV];}};return new F(function(){return _WR(_WL);});},_WW=new T(function(){return B(_WM(0));}),_WX=32,_WY=new T(function(){return [1,_WX,_WY];}),_WZ=function(_X0,_X1){var _X2=E(_X0);if(!_X2[0]){return [0];}else{var _X3=_X2[2],_X4=E(_X1);if(!_X4[0]){return [0];}else{var _X5=_X4[2],_X6=new T(function(){return B(_WZ(_X3,_X5));});return [1,[0,_X2[1],_X4[1]],_X6];}}},_X7=new T(function(){return B(_WZ(_WW,_WY));}),_X8=new T(function(){return B(_Wv(_X7));}),_X9=35,_Xa=function(_Xb){return E(E(_Xb)[1]);},_Xc=function(_Xd,_Xe,_Xf){while(1){var _Xg=E(_Xf);if(!_Xg[0]){return false;}else{if(!B(A(_Xa,[_Xd,_Xe,_Xg[1]]))){_Xf=_Xg[2];continue;}else{return true;}}}},_Xh=function(_Xi){return E(E(_Xi)[1]);},_Xj=function(_Xk){var _Xl=E(_Xk);if(!_Xl[0]){return [0];}else{var _Xm=_Xl[2],_Xn=new T(function(){return B(_Xj(_Xm));},1);return new F(function(){return _1t(_Xl[1],_Xn);});}},_Xo=function(_Xp){return new F(function(){return _jY("Dungeon.hs:(127,5)-(128,21)|function tup");});},_Xq=new T(function(){return B(_Xo(_));}),_Xr=function(_Xs){var _Xt=E(_Xs);if(!_Xt[0]){return E(_Xq);}else{var _Xu=_Xt[1],_Xv=E(_Xt[2]);return (_Xv[0]==0)?[0,_Xu,_Xu]:(E(_Xv[2])[0]==0)?[0,_Xu,_Xv[1]]:E(_Xq);}},_Xw=function(_Xx,_Xy){return new F(function(){return _a6(E(E(_Xx)[2]),E(E(_Xy)[2]));});},_Xz=function(_XA){var _XB=E(_XA);if(!_XB[0]){return [0];}else{var _XC=_XB[2],_XD=new T(function(){return B(_Xz(_XC));}),_XE=function(_XF){var _XG=E(_XF);if(!_XG[0]){return E(_XD);}else{var _XH=_XG[1],_XI=_XG[2],_XJ=new T(function(){return B(_XE(_XI));}),_XK=new T(function(){return B(_Xr(_XH));});return [1,_XK,_XJ];}};return new F(function(){return _XE(B(_M7(2,B(_cm(_Xw,_XB[1])))));});}},_XL=function(_XM,_XN){var _XO=E(_XN);if(!_XO[0]){return [0];}else{var _XP=_XO[1],_XQ=_XO[2],_XR=new T(function(){var _XS=new T(function(){return B(A(_XM,[_XP]));}),_XT=B(_jy(_XS,_XQ));return [0,_XT[1],_XT[2]];}),_XU=new T(function(){return B(_XL(_XM,E(_XR)[2]));}),_XV=new T(function(){return E(E(_XR)[1]);});return [1,[1,_XP,_XV],_XU];}},_XW=function(_XX,_XY){return E(E(_XX)[1])==E(E(_XY)[1]);},_XZ=function(_Y0,_Y1){return new F(function(){return _a6(E(E(_Y0)[1]),E(E(_Y1)[1]));});},_Y2=45,_Y3=function(_Y4,_Y5){return E(E(_Y4)[2])==E(E(_Y5)[2]);},_Y6=function(_Y7,_Y8,_Y9,_Ya){var _Yb=E(_Ya);if(!_Yb[0]){var _Yc=_Yb[3],_Yd=_Yb[4],_Ye=_Yb[5],_Yf=E(_Yb[2]),_Yg=E(_Yf[1]);if(_Y7>=_Yg){if(_Y7!=_Yg){return new F(function(){return _ws(_Yf,_Yc,_Yd,B(_Y6(_Y7,_Y8,_Y9,_Ye)));});}else{var _Yh=E(_Yf[2]);if(_Y8>=_Yh){if(_Y8!=_Yh){return new F(function(){return _ws(_Yf,_Yc,_Yd,B(_Y6(_Y7,_Y8,_Y9,_Ye)));});}else{return [0,_Yb[1],[0,_Y7,_Y8],_Y9,E(_Yd),E(_Ye)];}}else{return new F(function(){return _vJ(_Yf,_Yc,B(_Y6(_Y7,_Y8,_Y9,_Yd)),_Ye);});}}}else{return new F(function(){return _vJ(_Yf,_Yc,B(_Y6(_Y7,_Y8,_Y9,_Yd)),_Ye);});}}else{return [0,1,[0,_Y7,_Y8],_Y9,E(_vE),E(_vE)];}},_Yi=function(_Yj,_Yk,_Yl,_Ym){var _Yn=E(_Ym);if(!_Yn[0]){var _Yo=_Yn[3],_Yp=_Yn[4],_Yq=_Yn[5],_Yr=E(_Yn[2]),_Ys=E(_Yr[1]);if(_Yj>=_Ys){if(_Yj!=_Ys){return new F(function(){return _ws(_Yr,_Yo,_Yp,B(_Yi(_Yj,_Yk,_Yl,_Yq)));});}else{var _Yt=E(_Yk),_Yu=E(_Yr[2]);if(_Yt>=_Yu){if(_Yt!=_Yu){return new F(function(){return _ws(_Yr,_Yo,_Yp,B(_Y6(_Yj,_Yt,_Yl,_Yq)));});}else{return [0,_Yn[1],[0,_Yj,_Yt],_Yl,E(_Yp),E(_Yq)];}}else{return new F(function(){return _vJ(_Yr,_Yo,B(_Y6(_Yj,_Yt,_Yl,_Yp)),_Yq);});}}}else{return new F(function(){return _vJ(_Yr,_Yo,B(_Yi(_Yj,_Yk,_Yl,_Yp)),_Yq);});}}else{return [0,1,[0,_Yj,_Yk],_Yl,E(_vE),E(_vE)];}},_Yv=function(_Yw,_Yx,_Yy){var _Yz=new T(function(){return [1,_Yw,_Yz];}),_YA=function(_YB){var _YC=E(_YB);if(!_YC[0]){return E(_Yy);}else{var _YD=E(_YC[1]),_YE=E(_YD[1]),_YF=E(_YD[2]),_YG=E(_YE[1]),_YH=E(_YF[1]),_YI=B(_YA(_YC[2]));if(_YG<=_YH){var _YJ=B(_uP(E(_YE[2]),E(_YF[2]))),_YK=function(_YL,_YM){var _YN=new T(function(){return _YL==_YH;}),_YO=function(_YP,_YQ){var _YR=E(_YP);if(!_YR[0]){if(!E(_YN)){return new F(function(){return _YK(_YL+1|0,_YQ);});}else{return E(_YI);}}else{var _YS=E(_YQ);if(!_YS[0]){return E(_YI);}else{return new F(function(){return _Yi(_YL,_YR[1],_YS[1],B(_YO(_YR[2],_YS[2])));});}}};return new F(function(){return _YO(_YJ,_YM);});};return new F(function(){return _YK(_YG,_Yz);});}else{return E(_YI);}}};return new F(function(){return _YA(_Yx);});},_YT=function(_YU){return E(E(_YU)[2]);},_YV=function(_){var _YW=B(_OD(0,_)),_YX=B(_ON(_YW,_)),_YY=_YX,_YZ=B(_Qs(_YW,_YY,_)),_Z0=_YZ,_Z1=B(_R5(_YW,_YY,_)),_Z2=_Z1,_Z3=B(_RI(_YW,_YY,_)),_Z4=_Z3,_Z5=B(_Sl(_YW,_YY,_)),_Z6=_Z5;return new T(function(){var _Z7=new T(function(){var _Z8=new T(function(){var _Z9=new T(function(){return B(_Xj(_Z6));}),_Za=function(_Zb){var _Zc=E(_Zb);if(!_Zc[0]){return E(_Z9);}else{var _Zd=_Zc[2],_Ze=new T(function(){return B(_Za(_Zd));},1);return new F(function(){return _1t(_Zc[1],_Ze);});}};return B(_Za(_Z4));}),_Zf=function(_Zg){var _Zh=E(_Zg);if(!_Zh[0]){return E(_Z8);}else{var _Zi=_Zh[2],_Zj=new T(function(){return B(_Zf(_Zi));},1);return new F(function(){return _1t(_Zh[1],_Zj);});}};return B(_Zf(_Z2));}),_Zk=function(_Zl){var _Zm=E(_Zl);if(!_Zm[0]){return E(_Z7);}else{var _Zn=_Zm[2],_Zo=new T(function(){return B(_Zk(_Zn));},1);return new F(function(){return _1t(_Zm[1],_Zo);});}},_Zp=B(_Zk(_Z0)),_Zq=B(_v9(_Xh,_Zp)),_Zr=new T(function(){return B(_v9(_YT,_Zp));}),_Zs=new T(function(){var _Zt=function(_Zu){while(1){var _Zv=(function(_Zw){var _Zx=E(_Zw);if(!_Zx[0]){return [0];}else{var _Zy=_Zx[2],_Zz=E(_Zx[1]),_ZA=E(_Zz[1]),_ZB=E(_Zz[2]);if(E(_ZA[2])!=E(_ZB[2])){_Zu=_Zy;return null;}else{var _ZC=new T(function(){return B(_Zt(_Zy));}),_ZD=new T(function(){if(!B(_Xc(_lU,_ZA,_Zr))){return E(_ZB);}else{return E(_ZA);}});return [1,_ZD,_ZC];}}})(_Zu);if(_Zv!=null){return _Zv;}}};return B(_Xz(B(_XL(_XW,B(_cm(_XZ,B(_Zt(_Zq))))))));}),_ZE=function(_ZF){var _ZG=E(_ZF);if(!_ZG[0]){return E(_Zs);}else{var _ZH=_ZG[2],_ZI=new T(function(){return B(_ZE(_ZH));}),_ZJ=function(_ZK){var _ZL=E(_ZK);if(!_ZL[0]){return E(_ZI);}else{var _ZM=_ZL[1],_ZN=_ZL[2],_ZO=new T(function(){return B(_ZJ(_ZN));}),_ZP=new T(function(){return B(_Xr(_ZM));});return [1,_ZP,_ZO];}};return new F(function(){return _ZJ(B(_M7(2,B(_cm(_XZ,_ZG[1])))));});}},_ZQ=function(_ZR){while(1){var _ZS=(function(_ZT){var _ZU=E(_ZT);if(!_ZU[0]){return [0];}else{var _ZV=_ZU[2],_ZW=E(_ZU[1]),_ZX=E(_ZW[1]),_ZY=E(_ZW[2]);if(E(_ZX[1])!=E(_ZY[1])){_ZR=_ZV;return null;}else{var _ZZ=new T(function(){return B(_ZQ(_ZV));}),_100=new T(function(){if(!B(_Xc(_lU,_ZX,_Zr))){return E(_ZY);}else{return E(_ZX);}});return [1,_100,_ZZ];}}})(_ZR);if(_ZS!=null){return _ZS;}}},_101=B(_Yv(_X9,_YY,B(_Yv(_Y2,_Zq,B(_Yv(_Y2,B(_ZE(B(_XL(_Y3,B(_cm(_Xw,B(_ZQ(_Zq)))))))),_X8)))))),_102=function(_103){var _104=E(_103);if(!_104[0]){return E(_101);}else{var _105=_104[2],_106=E(_104[1]),_107=E(_106[1]),_108=E(_106[2]);if(!B(_Xc(_lU,_107,_Zr))){return new F(function(){return _Mg(_107[1],_107[2],_X9,B(_102(_105)));});}else{return new F(function(){return _Mg(_108[1],_108[2],_X9,B(_102(_105)));});}}};return B(_102(_Zq));});},_109=function(_10a,_10b){return new F(function(){return _6W(_10a,E(_10b));});},_10c=function(_10d,_10e){while(1){var _10f=E(_10d);if(!_10f[0]){return E(_10e);}else{_10d=_10f[2];var _10g=_10e+1|0;_10e=_10g;continue;}}},_10h=new T(function(){return B(unCStr("Map.!: given key is not an element in the map"));}),_10i=new T(function(){return B(err(_10h));}),_10j=function(_10k,_10l,_10m){while(1){var _10n=E(_10m);if(!_10n[0]){var _10o=_10n[4],_10p=_10n[5],_10q=E(_10n[2]),_10r=E(_10q[1]);if(_10k>=_10r){if(_10k!=_10r){_10m=_10p;continue;}else{var _10s=E(_10q[2]);if(_10l>=_10s){if(_10l!=_10s){_10m=_10p;continue;}else{return E(_10n[3]);}}else{_10m=_10o;continue;}}}else{_10m=_10o;continue;}}else{return E(_10i);}}},_10t=function(_10u,_10v,_10w){while(1){var _10x=E(_10w);if(!_10x[0]){var _10y=_10x[4],_10z=_10x[5],_10A=E(_10x[2]),_10B=E(_10A[1]);if(_10u>=_10B){if(_10u!=_10B){_10w=_10z;continue;}else{var _10C=E(_10v),_10D=E(_10A[2]);if(_10C>=_10D){if(_10C!=_10D){return new F(function(){return _10j(_10u,_10C,_10z);});}else{return E(_10x[3]);}}else{return new F(function(){return _10j(_10u,_10C,_10y);});}}}else{_10w=_10y;continue;}}else{return E(_10i);}}},_10E=new T(function(){return B(_uP(0,20));}),_10F=function(_10G,_){var _10H=E(_N3)(),_10I=_10H;return new T(function(){var _10J=function(_10K){var _10L=E(_10K);if(!_10L[0]){return [0];}else{var _10M=_10L[2],_10N=new T(function(){return B(_10J(_10M));}),_10O=E(_10E);if(!_10O[0]){return E(_10N);}else{var _10P=_10O[1],_10Q=_10O[2],_10R=E(_10L[1]),_10S=_10R;if(E(B(_10t(_10S,_10P,_10G)))==35){var _10T=new T(function(){var _10U=function(_10V){while(1){var _10W=(function(_10X){var _10Y=E(_10X);if(!_10Y[0]){return E(_10N);}else{var _10Z=_10Y[1],_110=_10Y[2];if(E(B(_10t(_10S,_10Z,_10G)))==35){var _111=new T(function(){return B(_10U(_110));});return [1,[0,_10R,_10Z],_111];}else{_10V=_110;return null;}}})(_10V);if(_10W!=null){return _10W;}}};return B(_10U(_10Q));});return [1,[0,_10R,_10P],_10T];}else{var _112=function(_113){while(1){var _114=(function(_115){var _116=E(_115);if(!_116[0]){return E(_10N);}else{var _117=_116[1],_118=_116[2];if(E(B(_10t(_10S,_117,_10G)))==35){var _119=new T(function(){return B(_112(_118));});return [1,[0,_10R,_117],_119];}else{_113=_118;return null;}}})(_113);if(_114!=null){return _114;}}};return new F(function(){return _112(_10Q);});}}}},_11a=B(_10J(_10E));return B(_109(_11a,B(_MN(0,B(_10c(_11a,0))-1|0,_10I))[1]));});},_11b=function(_11c){var _11d=new T(function(){var _11e=E(_11c);if(_11e==255){return [0];}else{var _11f=B(_11b(_11e+1|0));return [1,_11f[1],_11f[2]];}});return [0,[0,_11c,_LF],_11d];},_11g=[2],_11h=function(_11i,_11j){while(1){var _11k=E(_11j);if(!_11k[0]){return E(_11i);}else{var _11l=E(_11k[1]),_11m=B(_Le(E(_11l[1]),_11l[2],_11i));_11j=_11k[2];_11i=_11m;continue;}}},_11n=new T(function(){var _11o=B(_11b(0));return B(_11h(_11g,[1,_11o[1],_11o[2]]));}),_11p=30,_11q=1,_11r=10,_11s=20,_11t=new T(function(){return B(unCStr("\u30c7\u30d3\u30eb\u30a8\u30f3\u30da\u30e9\u30fc"));}),_11u=0,_11v=new T(function(){return B(_uP(0,2147483647));}),_11w=0,_11x=[1,_11w,_17],_11y=[1,_11w,_11x],_11z=[1,_11w,_11y],_11A=new T(function(){return B(_WZ(_11v,_11z));}),_11B=new T(function(){return B(_11h(_11g,_11A));}),_11C=new T(function(){return B(_10c(_11z,0));}),_11D=[0,_11u,_11C,_11B],_11E=5000,_11F=40,_11G=[0,_11t,_11s,_11s,_11s,_11r,_11F,_11p,_11q,_11E,_11E,_11F,_11F,_11D],_11H=[1,_11G,_17],_11I=new T(function(){return B(_WZ(_11v,_17));}),_11J=new T(function(){return B(_11h(_11g,_11I));}),_11K=new T(function(){return B(_10c(_17,0));}),_11L=[0,_11u,_11K,_11J],_11M=85,_11N=60,_11O=150,_11P=50,_11Q=new T(function(){return B(unCStr("\u885b\u5175"));}),_11R=[0,_11Q,_11M,_11P,_11F,_11N,_11p,_11r,_11q,_11O,_11O,_11p,_11p,_11L],_11S=[1,_11R,_17],_11T=new T(function(){return B(unCStr("\u72c2\u4eba"));}),_11U=[0,_11T,_11M,_11u,_11u,_11p,_11r,_11N,_11q,_11O,_11O,_11u,_11u,_11L],_11V=[1,_11U,_11S],_11W=80,_11X=65,_11Y=100,_11Z=120,_120=new T(function(){return B(unCStr("\u30d7\u30ea\u30f3\u30bb\u30b9"));}),_121=[0,_120,_11r,_11W,_11X,_11F,_11P,_11s,_11q,_11Z,_11Z,_11Y,_11Y,_11L],_122=[1,_121,_11V],_123=[0,_122,_11H,_uG],_124=46,_125=new T(function(){return [1,_124,_125];}),_126=new T(function(){return B(_WZ(_WW,_125));}),_127=new T(function(){return B(_Wv(_126));}),_128=(function(e,c) {return e.classList.contains(c);}),_129=new T(function(){return B(unCStr("active"));}),_12a=function(_){return _9W;},_12b=function(_){var _12c=B(_YV(_)),_12d=B(_10F(_12c,_)),_12e=nMV([0,_11n,_12d,_12d,_12c,_127,_uG,_123]),_12f=_12e,_12g=rMV(_12f),_12h=_12f,_12i=function(_12j,_){var _12k=rMV(_12f),_12l=_12k,_12m=new T(function(){var _12n=E(_12l),_12o=_12n[1],_12p=new T(function(){return B(_Le(E(_12j)[1],_LI,_12o));});return [0,_12p,_12n[2],_12n[3],_12n[4],_12n[5],_12n[6],_12n[7]];}),_=wMV(_12f,_12m),_12q=E(_uw),_12r=jsFind(_12q);if(!_12r[0]){return new F(function(){return _ym(_12q);});}else{var _12s=E(_uK),_12t=_12s(E(_12r[1])),_12u=_12s(_12t),_12v=E(_128)(_12u,toJSStr(E(_129)));if(!_12v){return _9W;}else{var _12w=rMV(_12f),_12x=E(_12w),_12y=B(_yp(_12h,_12x[1],_12x[2],_12x[4],_12x[5],_12x[6],_12x[7],_)),_=wMV(_12f,E(E(_12y)[2]));return _9W;}}},_12z=B(A(_kp,[_3b,_w,_r,_uH,_LG,_12i,_])),_12A=function(_12B,_){var _12C=rMV(_12f),_12D=_12C,_12E=new T(function(){var _12F=E(_12D),_12G=_12F[1],_12H=new T(function(){return B(_Le(E(_12B)[1],_LF,_12G));});return [0,_12H,_12F[2],_12F[3],_12F[4],_12F[5],_12F[6],_12F[7]];}),_=wMV(_12f,_12E);return _9W;},_12I=B(A(_kp,[_3b,_w,_r,_uH,_LH,_12A,_])),_12J=rMV(_12f),_12K=E(_12J),_12L=B(_yp(_12h,_12K[1],_12K[2],_12K[4],_12K[5],_12K[6],_12K[7],_)),_=wMV(_12f,E(E(_12L)[2])),_12M="battle",_12N=jsFind(_12M);if(!_12N[0]){return new F(function(){return _ym(_12M);});}else{return new F(function(){return _kX(_12N[1],_12f,_12a,_);});}},_12O=function(_){return new F(function(){return _12b(_);});};
var hasteMain = function() {B(A(_12O, [0]));};window.onload = hasteMain;