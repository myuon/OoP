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

var _0="metaKey",_1="shiftKey",_2="altKey",_3="ctrlKey",_4="keyCode",_5=function(_6,_){var _7=_6[E(_4)],_8=_7,_9=_6[E(_3)],_a=_9,_b=_6[E(_2)],_c=_b,_d=_6[E(_1)],_e=_d,_f=_6[E(_0)],_g=_f;return new T(function(){var _h=Number(_8),_i=jsTrunc(_h);return [0,_i,E(_a),E(_c),E(_e),E(_g)];});},_j=function(_k,_l,_){return new F(function(){return _5(E(_l),_);});},_m="keydown",_n="keyup",_o="keypress",_p=function(_q){switch(E(_q)){case 0:return E(_o);case 1:return E(_n);default:return E(_m);}},_r=[0,_p,_j],_s="deltaZ",_t="deltaY",_u="deltaX",_v=function(_w,_x){var _y=E(_w);if(!_y[0]){return E(_x);}else{var _z=_y[2],_A=new T(function(){return B(_v(_z,_x));});return [1,_y[1],_A];}},_B=function(_C,_D){var _E=jsShowI(_C);return new F(function(){return _v(fromJSStr(_E),_D);});},_F=41,_G=40,_H=function(_I,_J,_K){if(_J>=0){return new F(function(){return _B(_J,_K);});}else{if(_I<=6){return new F(function(){return _B(_J,_K);});}else{var _L=new T(function(){var _M=jsShowI(_J);return B(_v(fromJSStr(_M),[1,_F,_K]));});return [1,_G,_L];}}},_N=new T(function(){return B(unCStr(")"));}),_O=new T(function(){return B(_H(0,2,_N));}),_P=new T(function(){return B(unAppCStr(") is outside of enumeration\'s range (0,",_O));}),_Q=function(_R){var _S=new T(function(){return B(_H(0,_R,_P));});return new F(function(){return err(B(unAppCStr("toEnum{MouseButton}: tag (",_S)));});},_T=function(_U,_){return new T(function(){var _V=Number(E(_U)),_W=jsTrunc(_V);if(_W<0){return B(_Q(_W));}else{if(_W>2){return B(_Q(_W));}else{return _W;}}});},_X=0,_Y=[0,_X,_X,_X],_Z="button",_10=new T(function(){return jsGetMouseCoords;}),_11=[0],_12=function(_13,_){var _14=E(_13);if(!_14[0]){return _11;}else{var _15=_14[1],_16=B(_12(_14[2],_)),_17=new T(function(){var _18=Number(E(_15));return jsTrunc(_18);});return [1,_17,_16];}},_19=function(_1a,_){var _1b=__arr2lst(0,_1a);return new F(function(){return _12(_1b,_);});},_1c=function(_1d,_){return new F(function(){return _19(E(_1d),_);});},_1e=function(_1f,_){return new T(function(){var _1g=Number(E(_1f));return jsTrunc(_1g);});},_1h=[0,_1e,_1c],_1i=function(_1j,_){var _1k=E(_1j);if(!_1k[0]){return _11;}else{var _1l=B(_1i(_1k[2],_));return [1,_1k[1],_1l];}},_1m=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_1n=new T(function(){return B(unCStr("base"));}),_1o=new T(function(){return B(unCStr("IOException"));}),_1p=new T(function(){var _1q=hs_wordToWord64(4053623282),_1r=hs_wordToWord64(3693590983);return [0,_1q,_1r,[0,_1q,_1r,_1n,_1m,_1o],_11,_11];}),_1s=function(_1t){return E(_1p);},_1u=function(_1v){return E(E(_1v)[1]);},_1w=function(_1x,_1y,_1z){var _1A=B(A(_1x,[_])),_1B=B(A(_1y,[_])),_1C=hs_eqWord64(_1A[1],_1B[1]);if(!_1C){return [0];}else{var _1D=hs_eqWord64(_1A[2],_1B[2]);return (!_1D)?[0]:[1,_1z];}},_1E=function(_1F){var _1G=E(_1F);return new F(function(){return _1w(B(_1u(_1G[1])),_1s,_1G[2]);});},_1H=new T(function(){return B(unCStr(": "));}),_1I=new T(function(){return B(unCStr(")"));}),_1J=new T(function(){return B(unCStr(" ("));}),_1K=new T(function(){return B(unCStr("interrupted"));}),_1L=new T(function(){return B(unCStr("system error"));}),_1M=new T(function(){return B(unCStr("unsatisified constraints"));}),_1N=new T(function(){return B(unCStr("user error"));}),_1O=new T(function(){return B(unCStr("permission denied"));}),_1P=new T(function(){return B(unCStr("illegal operation"));}),_1Q=new T(function(){return B(unCStr("end of file"));}),_1R=new T(function(){return B(unCStr("resource exhausted"));}),_1S=new T(function(){return B(unCStr("resource busy"));}),_1T=new T(function(){return B(unCStr("does not exist"));}),_1U=new T(function(){return B(unCStr("already exists"));}),_1V=new T(function(){return B(unCStr("resource vanished"));}),_1W=new T(function(){return B(unCStr("timeout"));}),_1X=new T(function(){return B(unCStr("unsupported operation"));}),_1Y=new T(function(){return B(unCStr("hardware fault"));}),_1Z=new T(function(){return B(unCStr("inappropriate type"));}),_20=new T(function(){return B(unCStr("invalid argument"));}),_21=new T(function(){return B(unCStr("failed"));}),_22=new T(function(){return B(unCStr("protocol error"));}),_23=function(_24,_25){switch(E(_24)){case 0:return new F(function(){return _v(_1U,_25);});break;case 1:return new F(function(){return _v(_1T,_25);});break;case 2:return new F(function(){return _v(_1S,_25);});break;case 3:return new F(function(){return _v(_1R,_25);});break;case 4:return new F(function(){return _v(_1Q,_25);});break;case 5:return new F(function(){return _v(_1P,_25);});break;case 6:return new F(function(){return _v(_1O,_25);});break;case 7:return new F(function(){return _v(_1N,_25);});break;case 8:return new F(function(){return _v(_1M,_25);});break;case 9:return new F(function(){return _v(_1L,_25);});break;case 10:return new F(function(){return _v(_22,_25);});break;case 11:return new F(function(){return _v(_21,_25);});break;case 12:return new F(function(){return _v(_20,_25);});break;case 13:return new F(function(){return _v(_1Z,_25);});break;case 14:return new F(function(){return _v(_1Y,_25);});break;case 15:return new F(function(){return _v(_1X,_25);});break;case 16:return new F(function(){return _v(_1W,_25);});break;case 17:return new F(function(){return _v(_1V,_25);});break;default:return new F(function(){return _v(_1K,_25);});}},_26=new T(function(){return B(unCStr("}"));}),_27=new T(function(){return B(unCStr("{handle: "));}),_28=function(_29,_2a,_2b,_2c,_2d,_2e){var _2f=new T(function(){var _2g=new T(function(){var _2h=new T(function(){var _2i=E(_2c);if(!_2i[0]){return E(_2e);}else{var _2j=new T(function(){var _2k=new T(function(){return B(_v(_1I,_2e));},1);return B(_v(_2i,_2k));},1);return B(_v(_1J,_2j));}},1);return B(_23(_2a,_2h));},1),_2l=E(_2b);if(!_2l[0]){return E(_2g);}else{var _2m=new T(function(){return B(_v(_1H,_2g));},1);return B(_v(_2l,_2m));}},1),_2n=E(_2d);if(!_2n[0]){var _2o=E(_29);if(!_2o[0]){return E(_2f);}else{var _2p=E(_2o[1]);if(!_2p[0]){var _2q=_2p[1],_2r=new T(function(){var _2s=new T(function(){var _2t=new T(function(){return B(_v(_1H,_2f));},1);return B(_v(_26,_2t));},1);return B(_v(_2q,_2s));},1);return new F(function(){return _v(_27,_2r);});}else{var _2u=_2p[1],_2v=new T(function(){var _2w=new T(function(){var _2x=new T(function(){return B(_v(_1H,_2f));},1);return B(_v(_26,_2x));},1);return B(_v(_2u,_2w));},1);return new F(function(){return _v(_27,_2v);});}}}else{var _2y=new T(function(){return B(_v(_1H,_2f));},1);return new F(function(){return _v(_2n[1],_2y);});}},_2z=function(_2A){var _2B=E(_2A);return new F(function(){return _28(_2B[1],_2B[2],_2B[3],_2B[4],_2B[6],_11);});},_2C=function(_2D,_2E,_2F){var _2G=E(_2E);return new F(function(){return _28(_2G[1],_2G[2],_2G[3],_2G[4],_2G[6],_2F);});},_2H=function(_2I,_2J){var _2K=E(_2I);return new F(function(){return _28(_2K[1],_2K[2],_2K[3],_2K[4],_2K[6],_2J);});},_2L=44,_2M=93,_2N=91,_2O=function(_2P,_2Q,_2R){var _2S=E(_2Q);if(!_2S[0]){return new F(function(){return unAppCStr("[]",_2R);});}else{var _2T=_2S[1],_2U=_2S[2],_2V=new T(function(){var _2W=new T(function(){var _2X=[1,_2M,_2R],_2Y=function(_2Z){var _30=E(_2Z);if(!_30[0]){return E(_2X);}else{var _31=_30[1],_32=_30[2],_33=new T(function(){var _34=new T(function(){return B(_2Y(_32));});return B(A(_2P,[_31,_34]));});return [1,_2L,_33];}};return B(_2Y(_2U));});return B(A(_2P,[_2T,_2W]));});return [1,_2N,_2V];}},_35=function(_36,_37){return new F(function(){return _2O(_2H,_36,_37);});},_38=[0,_2C,_2z,_35],_39=new T(function(){return [0,_1s,_38,_3a,_1E,_2z];}),_3a=function(_3b){return [0,_39,_3b];},_3c=[0],_3d=7,_3e=new T(function(){return B(unCStr("Pattern match failure in do expression at src/Haste/Prim/Any.hs:272:5-9"));}),_3f=[0,_3c,_3d,_11,_3e,_3c,_3c],_3g=new T(function(){return B(_3a(_3f));}),_3h=function(_){return new F(function(){return die(_3g);});},_3i=function(_3j){return E(E(_3j)[1]);},_3k=function(_3l,_3m,_3n,_){var _3o=__arr2lst(0,_3n),_3p=B(_1i(_3o,_)),_3q=E(_3p);if(!_3q[0]){return new F(function(){return _3h(_);});}else{var _3r=E(_3q[2]);if(!_3r[0]){return new F(function(){return _3h(_);});}else{if(!E(_3r[2])[0]){var _3s=B(A(_3i,[_3l,_3q[1],_])),_3t=B(A(_3i,[_3m,_3r[1],_]));return [0,_3s,_3t];}else{return new F(function(){return _3h(_);});}}}},_3u=function(_){return new F(function(){return __jsNull();});},_3v=function(_3w){var _3x=B(A(_3w,[_]));return E(_3x);},_3y=new T(function(){return B(_3v(_3u));}),_3z=new T(function(){return E(_3y);}),_3A=function(_3B,_3C,_){if(E(_3B)==7){var _3D=E(_10)(_3C),_3E=B(_3k(_1h,_1h,_3D,_)),_3F=_3E,_3G=_3C[E(_u)],_3H=_3G,_3I=_3C[E(_t)],_3J=_3I,_3K=_3C[E(_s)],_3L=_3K;return new T(function(){return [0,E(_3F),E(_3c),[0,_3H,_3J,_3L]];});}else{var _3M=E(_10)(_3C),_3N=B(_3k(_1h,_1h,_3M,_)),_3O=_3N,_3P=_3C[E(_Z)],_3Q=__eq(_3P,E(_3z));if(!E(_3Q)){var _3R=B(_T(_3P,_)),_3S=_3R;return new T(function(){return [0,E(_3O),[1,_3S],E(_Y)];});}else{return new T(function(){return [0,E(_3O),E(_3c),E(_Y)];});}}},_3T=function(_3U,_3V,_){return new F(function(){return _3A(_3U,E(_3V),_);});},_3W="mouseout",_3X="mouseover",_3Y="mousemove",_3Z="mouseup",_40="mousedown",_41="dblclick",_42="click",_43="wheel",_44=function(_45){switch(E(_45)){case 0:return E(_42);case 1:return E(_41);case 2:return E(_40);case 3:return E(_3Z);case 4:return E(_3Y);case 5:return E(_3X);case 6:return E(_3W);default:return E(_43);}},_46=[0,_44,_3T],_47=function(_48,_){return [1,_48];},_49=function(_4a){return E(_4a);},_4b=[0,_49,_47],_4c=function(_4d,_4e,_){var _4f=B(A(_4d,[_])),_4g=B(A(_4e,[_]));return _4f;},_4h=function(_4i,_4j,_){var _4k=B(A(_4i,[_])),_4l=_4k,_4m=B(A(_4j,[_])),_4n=_4m;return new T(function(){return B(A(_4l,[_4n]));});},_4o=function(_4p,_4q,_){var _4r=B(A(_4q,[_]));return _4p;},_4s=function(_4t,_4u,_){var _4v=B(A(_4u,[_])),_4w=_4v;return new T(function(){return B(A(_4t,[_4w]));});},_4x=[0,_4s,_4o],_4y=function(_4z,_){return _4z;},_4A=function(_4B,_4C,_){var _4D=B(A(_4B,[_]));return new F(function(){return A(_4C,[_]);});},_4E=[0,_4x,_4y,_4h,_4A,_4c],_4F=function(_4G,_4H,_){var _4I=B(A(_4G,[_]));return new F(function(){return A(_4H,[_4I,_]);});},_4J=function(_4K){return [0,_3c,_3d,_11,_4K,_3c,_3c];},_4L=function(_4M,_){var _4N=new T(function(){var _4O=new T(function(){return B(_4J(_4M));});return B(_3a(_4O));});return new F(function(){return die(_4N);});},_4P=[0,_4E,_4F,_4A,_4y,_4L],_4Q=[0,_4P,_49],_4R=[0,_4Q,_4y],_4S=function(_4T,_4U){return E(_4T)==E(_4U);},_4V=function(_4W,_4X){return E(_4W)!=E(_4X);},_4Y=[0,_4S,_4V],_4Z=function(_50,_51){var _52=E(_50),_53=E(_51);return (_52>_53)?E(_52):E(_53);},_54=function(_55,_56){var _57=E(_55),_58=E(_56);return (_57>_58)?E(_58):E(_57);},_59=function(_5a,_5b){return (_5a>=_5b)?(_5a!=_5b)?2:1:0;},_5c=function(_5d,_5e){return new F(function(){return _59(E(_5d),E(_5e));});},_5f=function(_5g,_5h){return E(_5g)>=E(_5h);},_5i=function(_5j,_5k){return E(_5j)>E(_5k);},_5l=function(_5m,_5n){return E(_5m)<=E(_5n);},_5o=function(_5p,_5q){return E(_5p)<E(_5q);},_5r=[0,_4Y,_5c,_5o,_5l,_5i,_5f,_4Z,_54],_5s=function(_5t,_5u){while(1){var _5v=E(_5t);if(!_5v[0]){return (E(_5u)[0]==0)?1:0;}else{var _5w=E(_5u);if(!_5w[0]){return 2;}else{var _5x=E(_5v[1]),_5y=E(_5w[1]);if(_5x!=_5y){return (_5x>_5y)?2:0;}else{_5t=_5v[2];_5u=_5w[2];continue;}}}}},_5z=[1],_5A=new T(function(){return B(unCStr("Failure in Data.Map.balanceR"));}),_5B=function(_5C){return new F(function(){return err(_5A);});},_5D=new T(function(){return B(_5B(_));}),_5E=function(_5F,_5G,_5H,_5I){var _5J=E(_5H);if(!_5J[0]){var _5K=_5J[1],_5L=E(_5I);if(!_5L[0]){var _5M=_5L[1],_5N=_5L[2],_5O=_5L[3];if(_5M<=(imul(3,_5K)|0)){return [0,(1+_5K|0)+_5M|0,E(_5F),_5G,E(_5J),E(_5L)];}else{var _5P=E(_5L[4]);if(!_5P[0]){var _5Q=_5P[1],_5R=_5P[2],_5S=_5P[3],_5T=_5P[4],_5U=_5P[5],_5V=E(_5L[5]);if(!_5V[0]){var _5W=_5V[1];if(_5Q>=(imul(2,_5W)|0)){var _5X=function(_5Y){var _5Z=E(_5F),_60=E(_5U);return (_60[0]==0)?[0,(1+_5K|0)+_5M|0,E(_5R),_5S,[0,(1+_5K|0)+_5Y|0,E(_5Z),_5G,E(_5J),E(_5T)],[0,(1+_5W|0)+_60[1]|0,E(_5N),_5O,E(_60),E(_5V)]]:[0,(1+_5K|0)+_5M|0,E(_5R),_5S,[0,(1+_5K|0)+_5Y|0,E(_5Z),_5G,E(_5J),E(_5T)],[0,1+_5W|0,E(_5N),_5O,E(_5z),E(_5V)]];},_61=E(_5T);if(!_61[0]){return new F(function(){return _5X(_61[1]);});}else{return new F(function(){return _5X(0);});}}else{return [0,(1+_5K|0)+_5M|0,E(_5N),_5O,[0,(1+_5K|0)+_5Q|0,E(_5F),_5G,E(_5J),E(_5P)],E(_5V)];}}else{return E(_5D);}}else{return E(_5D);}}}else{return [0,1+_5K|0,E(_5F),_5G,E(_5J),E(_5z)];}}else{var _62=E(_5I);if(!_62[0]){var _63=_62[1],_64=_62[2],_65=_62[3],_66=_62[5],_67=E(_62[4]);if(!_67[0]){var _68=_67[1],_69=_67[2],_6a=_67[3],_6b=_67[4],_6c=_67[5],_6d=E(_66);if(!_6d[0]){var _6e=_6d[1];if(_68>=(imul(2,_6e)|0)){var _6f=function(_6g){var _6h=E(_5F),_6i=E(_6c);return (_6i[0]==0)?[0,1+_63|0,E(_69),_6a,[0,1+_6g|0,E(_6h),_5G,E(_5z),E(_6b)],[0,(1+_6e|0)+_6i[1]|0,E(_64),_65,E(_6i),E(_6d)]]:[0,1+_63|0,E(_69),_6a,[0,1+_6g|0,E(_6h),_5G,E(_5z),E(_6b)],[0,1+_6e|0,E(_64),_65,E(_5z),E(_6d)]];},_6j=E(_6b);if(!_6j[0]){return new F(function(){return _6f(_6j[1]);});}else{return new F(function(){return _6f(0);});}}else{return [0,1+_63|0,E(_64),_65,[0,1+_68|0,E(_5F),_5G,E(_5z),E(_67)],E(_6d)];}}else{return [0,3,E(_69),_6a,[0,1,E(_5F),_5G,E(_5z),E(_5z)],[0,1,E(_64),_65,E(_5z),E(_5z)]];}}else{var _6k=E(_66);return (_6k[0]==0)?[0,3,E(_64),_65,[0,1,E(_5F),_5G,E(_5z),E(_5z)],E(_6k)]:[0,2,E(_5F),_5G,E(_5z),E(_62)];}}else{return [0,1,E(_5F),_5G,E(_5z),E(_5z)];}}},_6l=function(_6m,_6n){return [0,1,E(_6m),_6n,E(_5z),E(_5z)];},_6o=function(_6p,_6q,_6r){var _6s=E(_6r);if(!_6s[0]){return new F(function(){return _5E(_6s[2],_6s[3],_6s[4],B(_6o(_6p,_6q,_6s[5])));});}else{return new F(function(){return _6l(_6p,_6q);});}},_6t=new T(function(){return B(unCStr("Failure in Data.Map.balanceL"));}),_6u=function(_6v){return new F(function(){return err(_6t);});},_6w=new T(function(){return B(_6u(_));}),_6x=function(_6y,_6z,_6A,_6B){var _6C=E(_6B);if(!_6C[0]){var _6D=_6C[1],_6E=E(_6A);if(!_6E[0]){var _6F=_6E[1],_6G=_6E[2],_6H=_6E[3];if(_6F<=(imul(3,_6D)|0)){return [0,(1+_6F|0)+_6D|0,E(_6y),_6z,E(_6E),E(_6C)];}else{var _6I=E(_6E[4]);if(!_6I[0]){var _6J=_6I[1],_6K=E(_6E[5]);if(!_6K[0]){var _6L=_6K[1],_6M=_6K[2],_6N=_6K[3],_6O=_6K[4],_6P=_6K[5];if(_6L>=(imul(2,_6J)|0)){var _6Q=function(_6R){var _6S=E(_6P);return (_6S[0]==0)?[0,(1+_6F|0)+_6D|0,E(_6M),_6N,[0,(1+_6J|0)+_6R|0,E(_6G),_6H,E(_6I),E(_6O)],[0,(1+_6D|0)+_6S[1]|0,E(_6y),_6z,E(_6S),E(_6C)]]:[0,(1+_6F|0)+_6D|0,E(_6M),_6N,[0,(1+_6J|0)+_6R|0,E(_6G),_6H,E(_6I),E(_6O)],[0,1+_6D|0,E(_6y),_6z,E(_5z),E(_6C)]];},_6T=E(_6O);if(!_6T[0]){return new F(function(){return _6Q(_6T[1]);});}else{return new F(function(){return _6Q(0);});}}else{return [0,(1+_6F|0)+_6D|0,E(_6G),_6H,E(_6I),[0,(1+_6D|0)+_6L|0,E(_6y),_6z,E(_6K),E(_6C)]];}}else{return E(_6w);}}else{return E(_6w);}}}else{return [0,1+_6D|0,E(_6y),_6z,E(_5z),E(_6C)];}}else{var _6U=E(_6A);if(!_6U[0]){var _6V=_6U[1],_6W=_6U[2],_6X=_6U[3],_6Y=_6U[5],_6Z=E(_6U[4]);if(!_6Z[0]){var _70=_6Z[1],_71=E(_6Y);if(!_71[0]){var _72=_71[1],_73=_71[2],_74=_71[3],_75=_71[4],_76=_71[5];if(_72>=(imul(2,_70)|0)){var _77=function(_78){var _79=E(_76);return (_79[0]==0)?[0,1+_6V|0,E(_73),_74,[0,(1+_70|0)+_78|0,E(_6W),_6X,E(_6Z),E(_75)],[0,1+_79[1]|0,E(_6y),_6z,E(_79),E(_5z)]]:[0,1+_6V|0,E(_73),_74,[0,(1+_70|0)+_78|0,E(_6W),_6X,E(_6Z),E(_75)],[0,1,E(_6y),_6z,E(_5z),E(_5z)]];},_7a=E(_75);if(!_7a[0]){return new F(function(){return _77(_7a[1]);});}else{return new F(function(){return _77(0);});}}else{return [0,1+_6V|0,E(_6W),_6X,E(_6Z),[0,1+_72|0,E(_6y),_6z,E(_71),E(_5z)]];}}else{return [0,3,E(_6W),_6X,E(_6Z),[0,1,E(_6y),_6z,E(_5z),E(_5z)]];}}else{var _7b=E(_6Y);return (_7b[0]==0)?[0,3,E(_7b[2]),_7b[3],[0,1,E(_6W),_6X,E(_5z),E(_5z)],[0,1,E(_6y),_6z,E(_5z),E(_5z)]]:[0,2,E(_6y),_6z,E(_6U),E(_5z)];}}else{return [0,1,E(_6y),_6z,E(_5z),E(_5z)];}}},_7c=function(_7d,_7e,_7f){var _7g=E(_7f);if(!_7g[0]){return new F(function(){return _6x(_7g[2],_7g[3],B(_7c(_7d,_7e,_7g[4])),_7g[5]);});}else{return new F(function(){return _6l(_7d,_7e);});}},_7h=function(_7i,_7j,_7k,_7l,_7m,_7n,_7o){return new F(function(){return _6x(_7l,_7m,B(_7c(_7i,_7j,_7n)),_7o);});},_7p=function(_7q,_7r,_7s,_7t,_7u,_7v,_7w,_7x){var _7y=E(_7s);if(!_7y[0]){var _7z=_7y[1],_7A=_7y[2],_7B=_7y[3],_7C=_7y[4],_7D=_7y[5];if((imul(3,_7z)|0)>=_7t){if((imul(3,_7t)|0)>=_7z){return [0,(_7z+_7t|0)+1|0,E(_7q),_7r,E(_7y),[0,_7t,E(_7u),_7v,E(_7w),E(_7x)]];}else{return new F(function(){return _5E(_7A,_7B,_7C,B(_7p(_7q,_7r,_7D,_7t,_7u,_7v,_7w,_7x)));});}}else{return new F(function(){return _6x(_7u,_7v,B(_7E(_7q,_7r,_7z,_7A,_7B,_7C,_7D,_7w)),_7x);});}}else{return new F(function(){return _7h(_7q,_7r,_7t,_7u,_7v,_7w,_7x);});}},_7E=function(_7F,_7G,_7H,_7I,_7J,_7K,_7L,_7M){var _7N=E(_7M);if(!_7N[0]){var _7O=_7N[1],_7P=_7N[2],_7Q=_7N[3],_7R=_7N[4],_7S=_7N[5];if((imul(3,_7H)|0)>=_7O){if((imul(3,_7O)|0)>=_7H){return [0,(_7H+_7O|0)+1|0,E(_7F),_7G,[0,_7H,E(_7I),_7J,E(_7K),E(_7L)],E(_7N)];}else{return new F(function(){return _5E(_7I,_7J,_7K,B(_7p(_7F,_7G,_7L,_7O,_7P,_7Q,_7R,_7S)));});}}else{return new F(function(){return _6x(_7P,_7Q,B(_7E(_7F,_7G,_7H,_7I,_7J,_7K,_7L,_7R)),_7S);});}}else{return new F(function(){return _6o(_7F,_7G,[0,_7H,E(_7I),_7J,E(_7K),E(_7L)]);});}},_7T=function(_7U,_7V,_7W,_7X){var _7Y=E(_7W);if(!_7Y[0]){var _7Z=_7Y[1],_80=_7Y[2],_81=_7Y[3],_82=_7Y[4],_83=_7Y[5],_84=E(_7X);if(!_84[0]){var _85=_84[1],_86=_84[2],_87=_84[3],_88=_84[4],_89=_84[5];if((imul(3,_7Z)|0)>=_85){if((imul(3,_85)|0)>=_7Z){return [0,(_7Z+_85|0)+1|0,E(_7U),_7V,E(_7Y),E(_84)];}else{return new F(function(){return _5E(_80,_81,_82,B(_7p(_7U,_7V,_83,_85,_86,_87,_88,_89)));});}}else{return new F(function(){return _6x(_86,_87,B(_7E(_7U,_7V,_7Z,_80,_81,_82,_83,_88)),_89);});}}else{return new F(function(){return _6o(_7U,_7V,_7Y);});}}else{return new F(function(){return _7c(_7U,_7V,_7X);});}},_8a=function(_8b,_8c,_8d,_8e){var _8f=E(_8b);if(_8f==1){var _8g=E(_8e);if(!_8g[0]){var _8h=new T(function(){return [0,1,E(_8c),_8d,E(_5z),E(_5z)];});return [0,_8h,_11,_11];}else{if(!B(_5s(_8c,E(_8g[1])[1]))){var _8i=new T(function(){return [0,1,E(_8c),_8d,E(_5z),E(_5z)];});return [0,_8i,_8g,_11];}else{var _8j=new T(function(){return [0,1,E(_8c),_8d,E(_5z),E(_5z)];});return [0,_8j,_11,_8g];}}}else{var _8k=B(_8a(_8f>>1,_8c,_8d,_8e)),_8l=_8k[1],_8m=_8k[3],_8n=E(_8k[2]);if(!_8n[0]){return [0,_8l,_11,_8m];}else{var _8o=E(_8n[1]),_8p=_8o[1],_8q=_8o[2],_8r=E(_8n[2]);if(!_8r[0]){var _8s=new T(function(){return B(_6o(_8p,_8q,_8l));});return [0,_8s,_11,_8m];}else{var _8t=E(_8r[1]),_8u=_8t[1];if(!B(_5s(_8p,_8u))){var _8v=B(_8a(_8f>>1,_8u,_8t[2],_8r[2])),_8w=_8v[1],_8x=new T(function(){return B(_7T(_8p,_8q,_8l,_8w));});return [0,_8x,_8v[2],_8v[3]];}else{return [0,_8l,_11,_8n];}}}}},_8y=function(_8z,_8A,_8B){var _8C=E(_8z),_8D=E(_8B);if(!_8D[0]){var _8E=_8D[2],_8F=_8D[3],_8G=_8D[4],_8H=_8D[5];switch(B(_5s(_8C,_8E))){case 0:return new F(function(){return _6x(_8E,_8F,B(_8y(_8C,_8A,_8G)),_8H);});break;case 1:return [0,_8D[1],E(_8C),_8A,E(_8G),E(_8H)];default:return new F(function(){return _5E(_8E,_8F,_8G,B(_8y(_8C,_8A,_8H)));});}}else{return [0,1,E(_8C),_8A,E(_5z),E(_5z)];}},_8I=function(_8J,_8K){while(1){var _8L=E(_8K);if(!_8L[0]){return E(_8J);}else{var _8M=E(_8L[1]),_8N=B(_8y(_8M[1],_8M[2],_8J));_8K=_8L[2];_8J=_8N;continue;}}},_8O=function(_8P,_8Q,_8R,_8S){return new F(function(){return _8I(B(_8y(_8Q,_8R,_8P)),_8S);});},_8T=function(_8U,_8V,_8W){var _8X=E(_8V);return new F(function(){return _8I(B(_8y(_8X[1],_8X[2],_8U)),_8W);});},_8Y=function(_8Z,_90,_91){while(1){var _92=E(_91);if(!_92[0]){return E(_90);}else{var _93=E(_92[1]),_94=_93[1],_95=_93[2],_96=E(_92[2]);if(!_96[0]){return new F(function(){return _6o(_94,_95,_90);});}else{var _97=E(_96[1]),_98=_97[1];if(!B(_5s(_94,_98))){var _99=B(_8a(_8Z,_98,_97[2],_96[2])),_9a=_99[1],_9b=E(_99[3]);if(!_9b[0]){var _9c=_8Z<<1,_9d=B(_7T(_94,_95,_90,_9a));_91=_99[2];_8Z=_9c;_90=_9d;continue;}else{return new F(function(){return _8T(B(_7T(_94,_95,_90,_9a)),_9b[1],_9b[2]);});}}else{return new F(function(){return _8O(_90,_94,_95,_96);});}}}}},_9e=function(_9f,_9g,_9h,_9i,_9j){var _9k=E(_9j);if(!_9k[0]){return new F(function(){return _6o(_9h,_9i,_9g);});}else{var _9l=E(_9k[1]),_9m=_9l[1];if(!B(_5s(_9h,_9m))){var _9n=B(_8a(_9f,_9m,_9l[2],_9k[2])),_9o=_9n[1],_9p=E(_9n[3]);if(!_9p[0]){return new F(function(){return _8Y(_9f<<1,B(_7T(_9h,_9i,_9g,_9o)),_9n[2]);});}else{return new F(function(){return _8T(B(_7T(_9h,_9i,_9g,_9o)),_9p[1],_9p[2]);});}}else{return new F(function(){return _8O(_9g,_9h,_9i,_9k);});}}},_9q=function(_9r){var _9s=E(_9r);if(!_9s[0]){return [1];}else{var _9t=E(_9s[1]),_9u=_9t[1],_9v=_9t[2],_9w=E(_9s[2]);if(!_9w[0]){return [0,1,E(_9u),_9v,E(_5z),E(_5z)];}else{var _9x=_9w[2],_9y=E(_9w[1]),_9z=_9y[1],_9A=_9y[2];if(!B(_5s(_9u,_9z))){return new F(function(){return _9e(1,[0,1,E(_9u),_9v,E(_5z),E(_5z)],_9z,_9A,_9x);});}else{return new F(function(){return _8O([0,1,E(_9u),_9v,E(_5z),E(_5z)],_9z,_9A,_9x);});}}}},_9B=new T(function(){return B(unCStr("}"));}),_9C=new T(function(){return B(unCStr(", "));}),_9D=new T(function(){return B(unCStr("Escape"));}),_9E=new T(function(){return B(unCStr("Defence"));}),_9F=new T(function(){return B(unCStr("Attack"));}),_9G=function(_9H){switch(E(_9H)){case 0:return E(_9F);case 1:return E(_9E);default:return E(_9D);}},_9I=function(_9J,_9K){switch(E(_9J)){case 0:return new F(function(){return _v(_9F,_9K);});break;case 1:return new F(function(){return _v(_9E,_9K);});break;default:return new F(function(){return _v(_9D,_9K);});}},_9L=function(_9M,_9N){return new F(function(){return _2O(_9I,_9M,_9N);});},_9O=function(_9P,_9Q,_9R){return new F(function(){return _9I(_9Q,_9R);});},_9S=[0,_9O,_9G,_9L],_9T=new T(function(){return B(unCStr("commandMap = "));}),_9U=new T(function(){return B(unCStr("listSize = "));}),_9V=new T(function(){return B(unCStr("index = "));}),_9W=new T(function(){return B(unCStr("CommandList {"));}),_9X=function(_9Y,_9Z,_a0){var _a1=new T(function(){return B(A(_9Z,[_a0]));});return new F(function(){return A(_9Y,[[1,_2L,_a1]]);});},_a2=new T(function(){return B(unCStr("fromList "));}),_a3=new T(function(){return B(unCStr(": empty list"));}),_a4=new T(function(){return B(unCStr("Prelude."));}),_a5=function(_a6){var _a7=new T(function(){return B(_v(_a6,_a3));},1);return new F(function(){return err(B(_v(_a4,_a7)));});},_a8=new T(function(){return B(unCStr("foldr1"));}),_a9=new T(function(){return B(_a5(_a8));}),_aa=function(_ab,_ac){var _ad=E(_ac);if(!_ad[0]){return E(_a9);}else{var _ae=_ad[1],_af=E(_ad[2]);if(!_af[0]){return E(_ae);}else{var _ag=new T(function(){return B(_aa(_ab,_af));});return new F(function(){return A(_ab,[_ae,_ag]);});}}},_ah=0,_ai=function(_aj){return E(E(_aj)[1]);},_ak=function(_al,_am){while(1){var _an=(function(_ao,_ap){var _aq=E(_ap);switch(_aq[0]){case 0:var _ar=_aq[4],_as=new T(function(){return B(_ak(_ao,_ar));});_al=_as;_am=_aq[3];return null;case 1:return [1,[0,_aq[1],_aq[2]],_ao];default:return E(_ao);}})(_al,_am);if(_an!=null){return _an;}}},_at=function(_au){var _av=E(_au);if(!_av[0]){var _aw=_av[3],_ax=_av[4];if(_av[2]>=0){var _ay=new T(function(){return B(_ak(_11,_ax));});return new F(function(){return _ak(_ay,_aw);});}else{var _az=new T(function(){return B(_ak(_11,_aw));});return new F(function(){return _ak(_az,_ax);});}}else{return new F(function(){return _ak(_11,_av);});}},_aA=function(_aB,_aC,_aD){var _aE=new T(function(){return B(_at(_aD));}),_aF=function(_aG,_aH){var _aI=E(_aG),_aJ=_aI[1],_aK=_aI[2],_aL=new T(function(){var _aM=new T(function(){return B(A(_ai,[_aB,_ah,_aK]));}),_aN=function(_aO){return new F(function(){return _H(0,E(_aJ),_aO);});};return B(A(_aa,[_9X,[1,_aN,[1,_aM,_11]],[1,_F,_aH]]));});return [1,_G,_aL];};if(_aC<=10){var _aP=function(_aQ){var _aR=new T(function(){return B(_2O(_aF,_aE,_aQ));},1);return new F(function(){return _v(_a2,_aR);});};return E(_aP);}else{var _aS=function(_aT){var _aU=new T(function(){var _aV=new T(function(){return B(_2O(_aF,_aE,[1,_F,_aT]));},1);return B(_v(_a2,_aV));});return [1,_G,_aU];};return E(_aS);}},_aW=function(_aX,_aY,_aZ,_b0){var _b1=new T(function(){return B(_aA(_9S,0,_b0));}),_b2=function(_b3){var _b4=new T(function(){var _b5=new T(function(){var _b6=new T(function(){var _b7=new T(function(){var _b8=new T(function(){var _b9=new T(function(){var _ba=new T(function(){var _bb=new T(function(){var _bc=new T(function(){return B(_v(_9B,_b3));});return B(A(_b1,[_bc]));},1);return B(_v(_9T,_bb));},1);return B(_v(_9C,_ba));});return B(_H(0,E(_aZ),_b9));},1);return B(_v(_9U,_b8));},1);return B(_v(_9C,_b7));});return B(_H(0,E(_aY),_b6));},1);return B(_v(_9V,_b5));},1);return new F(function(){return _v(_9W,_b4);});};if(_aX<11){return E(_b2);}else{var _bd=function(_be){var _bf=new T(function(){return B(_b2([1,_F,_be]));});return [1,_G,_bf];};return E(_bd);}},_bg=new T(function(){return B(unCStr("_commandList = "));}),_bh=new T(function(){return B(unCStr("_mp = "));}),_bi=new T(function(){return B(unCStr("_maxMP = "));}),_bj=new T(function(){return B(unCStr("_hp = "));}),_bk=new T(function(){return B(unCStr("_maxHP = "));}),_bl=new T(function(){return B(unCStr("_level = "));}),_bm=new T(function(){return B(unCStr("_luck = "));}),_bn=new T(function(){return B(unCStr("_agility = "));}),_bo=new T(function(){return B(unCStr("_vitality = "));}),_bp=new T(function(){return B(unCStr("_technique = "));}),_bq=new T(function(){return B(unCStr("_intelligence = "));}),_br=new T(function(){return B(unCStr("_strength = "));}),_bs=new T(function(){return B(unCStr("_name = "));}),_bt=new T(function(){return B(unCStr("Character {"));}),_bu=new T(function(){return B(unCStr("!!: negative index"));}),_bv=new T(function(){return B(_v(_a4,_bu));}),_bw=new T(function(){return B(err(_bv));}),_bx=new T(function(){return B(unCStr("!!: index too large"));}),_by=new T(function(){return B(_v(_a4,_bx));}),_bz=new T(function(){return B(err(_by));}),_bA=function(_bB,_bC){while(1){var _bD=E(_bB);if(!_bD[0]){return E(_bz);}else{var _bE=E(_bC);if(!_bE){return E(_bD[1]);}else{_bB=_bD[2];_bC=_bE-1|0;continue;}}}},_bF=function(_bG,_bH){if(_bH>=0){return new F(function(){return _bA(_bG,_bH);});}else{return E(_bw);}},_bI=new T(function(){return B(unCStr("ACK"));}),_bJ=new T(function(){return B(unCStr("BEL"));}),_bK=new T(function(){return B(unCStr("BS"));}),_bL=new T(function(){return B(unCStr("SP"));}),_bM=[1,_bL,_11],_bN=new T(function(){return B(unCStr("US"));}),_bO=[1,_bN,_bM],_bP=new T(function(){return B(unCStr("RS"));}),_bQ=[1,_bP,_bO],_bR=new T(function(){return B(unCStr("GS"));}),_bS=[1,_bR,_bQ],_bT=new T(function(){return B(unCStr("FS"));}),_bU=[1,_bT,_bS],_bV=new T(function(){return B(unCStr("ESC"));}),_bW=[1,_bV,_bU],_bX=new T(function(){return B(unCStr("SUB"));}),_bY=[1,_bX,_bW],_bZ=new T(function(){return B(unCStr("EM"));}),_c0=[1,_bZ,_bY],_c1=new T(function(){return B(unCStr("CAN"));}),_c2=[1,_c1,_c0],_c3=new T(function(){return B(unCStr("ETB"));}),_c4=[1,_c3,_c2],_c5=new T(function(){return B(unCStr("SYN"));}),_c6=[1,_c5,_c4],_c7=new T(function(){return B(unCStr("NAK"));}),_c8=[1,_c7,_c6],_c9=new T(function(){return B(unCStr("DC4"));}),_ca=[1,_c9,_c8],_cb=new T(function(){return B(unCStr("DC3"));}),_cc=[1,_cb,_ca],_cd=new T(function(){return B(unCStr("DC2"));}),_ce=[1,_cd,_cc],_cf=new T(function(){return B(unCStr("DC1"));}),_cg=[1,_cf,_ce],_ch=new T(function(){return B(unCStr("DLE"));}),_ci=[1,_ch,_cg],_cj=new T(function(){return B(unCStr("SI"));}),_ck=[1,_cj,_ci],_cl=new T(function(){return B(unCStr("SO"));}),_cm=[1,_cl,_ck],_cn=new T(function(){return B(unCStr("CR"));}),_co=[1,_cn,_cm],_cp=new T(function(){return B(unCStr("FF"));}),_cq=[1,_cp,_co],_cr=new T(function(){return B(unCStr("VT"));}),_cs=[1,_cr,_cq],_ct=new T(function(){return B(unCStr("LF"));}),_cu=[1,_ct,_cs],_cv=new T(function(){return B(unCStr("HT"));}),_cw=[1,_cv,_cu],_cx=[1,_bK,_cw],_cy=[1,_bJ,_cx],_cz=[1,_bI,_cy],_cA=new T(function(){return B(unCStr("ENQ"));}),_cB=[1,_cA,_cz],_cC=new T(function(){return B(unCStr("EOT"));}),_cD=[1,_cC,_cB],_cE=new T(function(){return B(unCStr("ETX"));}),_cF=[1,_cE,_cD],_cG=new T(function(){return B(unCStr("STX"));}),_cH=[1,_cG,_cF],_cI=new T(function(){return B(unCStr("SOH"));}),_cJ=[1,_cI,_cH],_cK=new T(function(){return B(unCStr("NUL"));}),_cL=[1,_cK,_cJ],_cM=92,_cN=new T(function(){return B(unCStr("\\DEL"));}),_cO=new T(function(){return B(unCStr("\\a"));}),_cP=new T(function(){return B(unCStr("\\\\"));}),_cQ=new T(function(){return B(unCStr("\\SO"));}),_cR=new T(function(){return B(unCStr("\\r"));}),_cS=new T(function(){return B(unCStr("\\f"));}),_cT=new T(function(){return B(unCStr("\\v"));}),_cU=new T(function(){return B(unCStr("\\n"));}),_cV=new T(function(){return B(unCStr("\\t"));}),_cW=new T(function(){return B(unCStr("\\b"));}),_cX=function(_cY,_cZ){if(_cY<=127){var _d0=E(_cY);switch(_d0){case 92:return new F(function(){return _v(_cP,_cZ);});break;case 127:return new F(function(){return _v(_cN,_cZ);});break;default:if(_d0<32){var _d1=E(_d0);switch(_d1){case 7:return new F(function(){return _v(_cO,_cZ);});break;case 8:return new F(function(){return _v(_cW,_cZ);});break;case 9:return new F(function(){return _v(_cV,_cZ);});break;case 10:return new F(function(){return _v(_cU,_cZ);});break;case 11:return new F(function(){return _v(_cT,_cZ);});break;case 12:return new F(function(){return _v(_cS,_cZ);});break;case 13:return new F(function(){return _v(_cR,_cZ);});break;case 14:var _d2=new T(function(){var _d3=E(_cZ);if(!_d3[0]){return [0];}else{if(E(_d3[1])==72){return B(unAppCStr("\\&",_d3));}else{return E(_d3);}}},1);return new F(function(){return _v(_cQ,_d2);});break;default:var _d4=new T(function(){return B(_bF(_cL,_d1));});return new F(function(){return _v([1,_cM,_d4],_cZ);});}}else{return [1,_d0,_cZ];}}}else{var _d5=new T(function(){var _d6=jsShowI(_cY),_d7=new T(function(){var _d8=E(_cZ);if(!_d8[0]){return [0];}else{var _d9=E(_d8[1]);if(_d9<48){return E(_d8);}else{if(_d9>57){return E(_d8);}else{return B(unAppCStr("\\&",_d8));}}}},1);return B(_v(fromJSStr(_d6),_d7));});return [1,_cM,_d5];}},_da=new T(function(){return B(unCStr("\\\""));}),_db=function(_dc,_dd){var _de=E(_dc);if(!_de[0]){return E(_dd);}else{var _df=_de[2],_dg=E(_de[1]);if(_dg==34){var _dh=new T(function(){return B(_db(_df,_dd));},1);return new F(function(){return _v(_da,_dh);});}else{var _di=new T(function(){return B(_db(_df,_dd));});return new F(function(){return _cX(_dg,_di);});}}},_dj=34,_dk=function(_dl,_dm,_dn,_do,_dp,_dq,_dr,_ds,_dt,_du,_dv,_dw,_dx,_dy){var _dz=new T(function(){var _dA=E(_dy);return B(_aW(0,_dA[1],_dA[2],_dA[3]));}),_dB=function(_dC){var _dD=new T(function(){var _dE=new T(function(){var _dF=new T(function(){var _dG=new T(function(){var _dH=new T(function(){var _dI=new T(function(){var _dJ=new T(function(){var _dK=new T(function(){var _dL=new T(function(){var _dM=new T(function(){var _dN=new T(function(){var _dO=new T(function(){var _dP=new T(function(){var _dQ=new T(function(){var _dR=new T(function(){var _dS=new T(function(){var _dT=new T(function(){var _dU=new T(function(){var _dV=new T(function(){var _dW=new T(function(){var _dX=new T(function(){var _dY=new T(function(){var _dZ=new T(function(){var _e0=new T(function(){var _e1=new T(function(){var _e2=new T(function(){var _e3=new T(function(){var _e4=new T(function(){var _e5=new T(function(){var _e6=new T(function(){var _e7=new T(function(){var _e8=new T(function(){var _e9=new T(function(){var _ea=new T(function(){var _eb=new T(function(){var _ec=new T(function(){var _ed=new T(function(){var _ee=new T(function(){var _ef=new T(function(){return B(_v(_9B,_dC));});return B(A(_dz,[_ef]));},1);return B(_v(_bg,_ee));},1);return B(_v(_9C,_ed));});return B(_H(0,E(_dx),_ec));},1);return B(_v(_bh,_eb));},1);return B(_v(_9C,_ea));});return B(_H(0,E(_dw),_e9));},1);return B(_v(_bi,_e8));},1);return B(_v(_9C,_e7));});return B(_H(0,E(_dv),_e6));},1);return B(_v(_bj,_e5));},1);return B(_v(_9C,_e4));});return B(_H(0,E(_du),_e3));},1);return B(_v(_bk,_e2));},1);return B(_v(_9C,_e1));});return B(_H(0,E(_dt),_e0));},1);return B(_v(_bl,_dZ));},1);return B(_v(_9C,_dY));});return B(_H(0,E(_ds),_dX));},1);return B(_v(_bm,_dW));},1);return B(_v(_9C,_dV));});return B(_H(0,E(_dr),_dU));},1);return B(_v(_bn,_dT));},1);return B(_v(_9C,_dS));});return B(_H(0,E(_dq),_dR));},1);return B(_v(_bo,_dQ));},1);return B(_v(_9C,_dP));});return B(_H(0,E(_dp),_dO));},1);return B(_v(_bp,_dN));},1);return B(_v(_9C,_dM));});return B(_H(0,E(_do),_dL));},1);return B(_v(_bq,_dK));},1);return B(_v(_9C,_dJ));});return B(_H(0,E(_dn),_dI));},1);return B(_v(_br,_dH));},1);return B(_v(_9C,_dG));});return B(_db(_dm,[1,_dj,_dF]));});return B(_v(_bs,[1,_dj,_dE]));},1);return new F(function(){return _v(_bt,_dD);});};if(_dl<11){return E(_dB);}else{var _eg=function(_eh){var _ei=new T(function(){return B(_dB([1,_F,_eh]));});return [1,_G,_ei];};return E(_eg);}},_ej=function(_ek){var _el=E(_ek);return new F(function(){return _dk(0,_el[1],_el[2],_el[3],_el[4],_el[5],_el[6],_el[7],_el[8],_el[9],_el[10],_el[11],_el[12],_el[13]);});},_em=function(_en){var _eo=E(_en);if(!_eo[0]){return [0,_11,_11];}else{var _ep=_eo[2],_eq=E(_eo[1]),_er=new T(function(){var _es=B(_em(_ep));return [0,_es[1],_es[2]];}),_et=new T(function(){return E(E(_er)[2]);}),_eu=new T(function(){return E(E(_er)[1]);});return [0,[1,_eq[1],_eu],[1,_eq[2],_et]];}},_ev=function(_ew){var _ex=E(_ew);if(!_ex[0]){return [0,_11,_11];}else{var _ey=_ex[2],_ez=E(_ex[1]),_eA=new T(function(){var _eB=B(_ev(_ey));return [0,_eB[1],_eB[2]];}),_eC=new T(function(){return E(E(_eA)[2]);}),_eD=new T(function(){return E(E(_eA)[1]);});return [0,[1,_ez[1],_eD],[1,_ez[2],_eC]];}},_eE=new T(function(){return B(unCStr("\n"));}),_eF=0,_eG=function(_eH,_eI,_){var _eJ=jsWriteHandle(E(_eH),toJSStr(E(_eI)));return _eF;},_eK=function(_eL,_eM,_){var _eN=E(_eL),_eO=jsWriteHandle(_eN,toJSStr(E(_eM)));return new F(function(){return _eG(_eN,_eE,_);});},_eP=function(_eQ,_eR){return new F(function(){return _59(E(E(E(_eQ)[2])[6]),E(E(E(_eR)[2])[6]));});},_eS=1,_eT=[0,_eS],_eU=new T(function(){return B(unCStr(" is not an element of the map"));}),_eV=function(_eW){var _eX=new T(function(){return B(_v(B(_H(0,_eW,_11)),_eU));});return new F(function(){return err(B(unAppCStr("IntMap.!: key ",_eX)));});},_eY=function(_eZ,_f0){var _f1=_eZ;while(1){var _f2=E(_f1);switch(_f2[0]){case 0:var _f3=_f2[2]>>>0;if(((_f0>>>0&((_f3-1>>>0^4294967295)>>>0^_f3)>>>0)>>>0&4294967295)==_f2[1]){if(!((_f0>>>0&_f3)>>>0)){_f1=_f2[3];continue;}else{_f1=_f2[4];continue;}}else{return new F(function(){return _eV(_f0);});}break;case 1:if(_f0!=_f2[1]){return new F(function(){return _eV(_f0);});}else{return E(_f2[2]);}break;default:return new F(function(){return _eV(_f0);});}}},_f4=0,_f5=function(_f6,_){var _f7=E(_f6);if(!_f7[0]){return _11;}else{var _f8=_f7[1],_f9=B(_f5(_f7[2],_)),_fa=new T(function(){return E(E(_f8)[13]);}),_fb=new T(function(){var _fc=E(_f8),_fd=new T(function(){var _fe=E(_fa),_ff=_fe[1],_fg=_fe[2],_fh=new T(function(){var _fi=E(_ff);if(_fi!=(E(_fg)-1|0)){return _fi+1|0;}else{return E(_f4);}});return [0,_fh,_fg,_fe[3]];});return [0,_fc[1],_fc[2],_fc[3],_fc[4],_fc[5],_fc[6],_fc[7],_fc[8],_fc[9],_fc[10],_fc[11],_fc[12],_fd];}),_fj=new T(function(){var _fk=E(_fa);return B(_eY(_fk[3],E(_fk[1])));});return [1,[0,_fj,_fb],_f9];}},_fl=function(_fm,_){var _fn=E(_fm);if(!_fn[0]){return _11;}else{var _fo=_fn[1],_fp=B(_fl(_fn[2],_)),_fq=new T(function(){return E(E(_fo)[13]);}),_fr=new T(function(){var _fs=E(_fo),_ft=new T(function(){var _fu=E(_fq),_fv=_fu[1],_fw=_fu[2],_fx=new T(function(){var _fy=E(_fv);if(_fy!=(E(_fw)-1|0)){return _fy+1|0;}else{return E(_f4);}});return [0,_fx,_fw,_fu[3]];});return [0,_fs[1],_fs[2],_fs[3],_fs[4],_fs[5],_fs[6],_fs[7],_fs[8],_fs[9],_fs[10],_fs[11],_fs[12],_ft];}),_fz=new T(function(){var _fA=E(_fq);return B(_eY(_fA[3],E(_fA[1])));});return [1,[0,_fz,_fr],_fp];}},_fB=function(_fC,_fD){return E(_fD);},_fE=function(_fF,_fG){return E(_fG);},_fH=[0,_fE,_fB],_fI=function(_fJ,_fK){return E(_fJ);},_fL=function(_fM){return E(_fM);},_fN=[0,_fL,_fI],_fO=function(_fP){return E(_fP);},_fQ=function(_fR,_fS){while(1){var _fT=E(_fS);if(!_fT[0]){return [0];}else{var _fU=_fT[2],_fV=E(_fR);if(_fV==1){return E(_fU);}else{_fR=_fV-1|0;_fS=_fU;continue;}}}},_fW=function(_fX){return E(E(_fX)[1]);},_fY=function(_fZ,_g0,_g1,_g2){var _g3=new T(function(){return E(_fZ)-1|0;}),_g4=new T(function(){return 0<E(_g3);}),_g5=new T(function(){var _g6=E(_fZ)+1|0;if(_g6>0){return B(_fQ(_g6,_g2));}else{return E(_g2);}}),_g7=new T(function(){var _g8=new T(function(){return B(_bF(_g2,E(_fZ)));});return B(A(_g1,[_g8]));}),_g9=function(_ga){var _gb=[1,_ga,_g5];if(!E(_g4)){return E(_gb);}else{var _gc=function(_gd,_ge){var _gf=E(_gd);if(!_gf[0]){return E(_gb);}else{var _gg=_gf[1],_gh=_gf[2],_gi=E(_ge);if(_gi==1){return [1,_gg,_gb];}else{var _gj=new T(function(){return B(_gc(_gh,_gi-1|0));});return [1,_gg,_gj];}}};return new F(function(){return _gc(_g2,E(_g3));});}};return new F(function(){return A(_fW,[_g0,_g9,_g7]);});},_gk=function(_gl,_gm,_gn,_go,_gp,_){while(1){var _gq=(function(_gr,_gs,_gt,_gu,_gv,_){var _gw=E(_gr);if(!_gw[0]){return [0,_eF,[0,_gs,_gt,_gu,_gv]];}else{var _gx=_gw[2],_gy=E(_gw[1]),_gz=_gy[2],_gA=E(_gy[1]);if(!_gA[0]){if(!E(_gA[1])){var _gB=new T(function(){var _gC=function(_gD){var _gE=E(_gD),_gF=_gE[10],_gG=new T(function(){return E(_gF)-((imul(E(E(_gz)[2]),5)|0)-(imul(E(B(_fY(_f4,_fH,_fO,_gs))[5]),2)|0)|0)|0;});return [0,_gE[1],_gE[2],_gE[3],_gE[4],_gE[5],_gE[6],_gE[7],_gE[8],_gE[9],_gG,_gE[11],_gE[12],_gE[13]];};return B(_fY(_f4,_fN,_gC,_gs));});_gl=_gx;_gm=_gB;var _gH=_gt,_gI=_gu,_gJ=_gv;_gn=_gH;_go=_gI;_gp=_gJ;return null;}else{var _gK=new T(function(){var _gL=function(_gM){var _gN=E(_gM),_gO=_gN[10],_gP=new T(function(){return E(_gO)-((imul(E(E(_gz)[2]),5)|0)-(imul(E(B(_fY(_f4,_fH,_fO,_gt))[5]),2)|0)|0)|0;});return [0,_gN[1],_gN[2],_gN[3],_gN[4],_gN[5],_gN[6],_gN[7],_gN[8],_gN[9],_gP,_gN[11],_gN[12],_gN[13]];};return B(_fY(_f4,_fN,_gL,_gt));});_gl=_gx;var _gQ=_gs;_gn=_gK;var _gI=_gu,_gJ=_gv;_gm=_gQ;_go=_gI;_gp=_gJ;return null;}}else{_gl=_gx;var _gQ=_gs,_gH=_gt,_gI=_gu,_gJ=_gv;_gm=_gQ;_gn=_gH;_go=_gI;_gp=_gJ;return null;}}})(_gl,_gm,_gn,_go,_gp,_);if(_gq!=null){return _gq;}}},_gR=0,_gS=[0,_gR],_gT=function(_gU,_gV){var _gW=E(_gU);if(!_gW[0]){return [0];}else{var _gX=_gW[1],_gY=_gW[2],_gZ=E(_gV);if(!_gZ[0]){return [0];}else{var _h0=_gZ[2],_h1=new T(function(){return B(_gT(_gY,_h0));}),_h2=new T(function(){var _h3=E(_gX);if(!_h3){return E(_gS);}else{return [1,_h3];}});return [1,[0,_h2,_gZ[1]],_h1];}}},_h4=[1,_11,_11],_h5=function(_h6,_h7){var _h8=function(_h9,_ha){var _hb=E(_h9);if(!_hb[0]){return E(_ha);}else{var _hc=_hb[1],_hd=_hb[2],_he=E(_ha);if(!_he[0]){return E(_hb);}else{var _hf=_he[1],_hg=_he[2];if(B(A(_h6,[_hc,_hf]))==2){var _hh=new T(function(){return B(_h8(_hb,_hg));});return [1,_hf,_hh];}else{var _hi=new T(function(){return B(_h8(_hd,_he));});return [1,_hc,_hi];}}}},_hj=function(_hk){var _hl=E(_hk);if(!_hl[0]){return [0];}else{var _hm=_hl[1],_hn=E(_hl[2]);if(!_hn[0]){return E(_hl);}else{var _ho=_hn[1],_hp=_hn[2],_hq=new T(function(){return B(_hj(_hp));}),_hr=new T(function(){return B(_h8(_hm,_ho));});return [1,_hr,_hq];}}},_hs=new T(function(){return B(_ht(B(_hj(_11))));}),_ht=function(_hu){while(1){var _hv=E(_hu);if(!_hv[0]){return E(_hs);}else{if(!E(_hv[2])[0]){return E(_hv[1]);}else{_hu=B(_hj(_hv));continue;}}}},_hw=new T(function(){return B(_hx(_11));}),_hy=function(_hz,_hA,_hB){while(1){var _hC=(function(_hD,_hE,_hF){var _hG=E(_hF);if(!_hG[0]){return [1,[1,_hD,_hE],_hw];}else{var _hH=_hG[1];if(B(A(_h6,[_hD,_hH]))==2){_hz=_hH;var _hI=[1,_hD,_hE];_hB=_hG[2];_hA=_hI;return null;}else{var _hJ=new T(function(){return B(_hx(_hG));});return [1,[1,_hD,_hE],_hJ];}}})(_hz,_hA,_hB);if(_hC!=null){return _hC;}}},_hK=function(_hL,_hM,_hN){while(1){var _hO=(function(_hP,_hQ,_hR){var _hS=E(_hR);if(!_hS[0]){var _hT=new T(function(){return B(A(_hQ,[[1,_hP,_11]]));});return [1,_hT,_hw];}else{var _hU=_hS[1],_hV=_hS[2];switch(B(A(_h6,[_hP,_hU]))){case 0:var _hW=function(_hX){return new F(function(){return A(_hQ,[[1,_hP,_hX]]);});};_hL=_hU;_hM=_hW;_hN=_hV;return null;case 1:var _hY=function(_hZ){return new F(function(){return A(_hQ,[[1,_hP,_hZ]]);});};_hL=_hU;_hM=_hY;_hN=_hV;return null;default:var _i0=new T(function(){return B(_hx(_hS));}),_i1=new T(function(){return B(A(_hQ,[[1,_hP,_11]]));});return [1,_i1,_i0];}}})(_hL,_hM,_hN);if(_hO!=null){return _hO;}}},_hx=function(_i2){var _i3=E(_i2);if(!_i3[0]){return E(_h4);}else{var _i4=_i3[1],_i5=E(_i3[2]);if(!_i5[0]){return [1,_i3,_11];}else{var _i6=_i5[1],_i7=_i5[2];if(B(A(_h6,[_i4,_i6]))==2){return new F(function(){return _hy(_i6,[1,_i4,_11],_i7);});}else{var _i8=function(_i9){return [1,_i4,_i9];};return new F(function(){return _hK(_i6,_i8,_i7);});}}}};return new F(function(){return _ht(B(_hx(_h7)));});},_ia=function(_){return new F(function(){return jsMkStdout();});},_ib=new T(function(){return B(_3v(_ia));}),_ic=function(_id,_ie,_if,_ig,_){var _ih=B(_fl(_id,_)),_ii=B(_ev(_ih)),_ij=_ii[1],_ik=_ii[2],_il=B(_f5(_ie,_)),_im=B(_em(_il))[2],_in=new T(function(){return B(_gT(_ij,_im));}),_io=function(_ip,_iq){var _ir=E(_ip);if(!_ir[0]){return E(_in);}else{var _is=_ir[1],_it=_ir[2],_iu=E(_iq);if(!_iu[0]){return E(_in);}else{var _iv=_iu[2],_iw=new T(function(){return B(_io(_it,_iv));}),_ix=new T(function(){var _iy=E(_is);if(!_iy){return E(_eT);}else{return [1,_iy];}});return [1,[0,_ix,_iu[1]],_iw];}}},_iz=new T(function(){return E(_if)+1|0;}),_iA=B(_gk(B(_h5(_eP,B(_io(_ij,_ik)))),_ik,_im,_iz,_ig,_)),_iB=E(E(_iA)[2]),_iC=B(_eK(_ib,B(_2O(_ej,_iB[1],_11)),_)),_iD=B(_eK(_ib,B(_2O(_ej,_iB[2],_11)),_));return [0,_iD,_iB];},_iE=function(_iF,_iG){if(_iF<=0){if(_iF>=0){return new F(function(){return quot(_iF,_iG);});}else{if(_iG<=0){return new F(function(){return quot(_iF,_iG);});}else{return quot(_iF+1|0,_iG)-1|0;}}}else{if(_iG>=0){if(_iF>=0){return new F(function(){return quot(_iF,_iG);});}else{if(_iG<=0){return new F(function(){return quot(_iF,_iG);});}else{return quot(_iF+1|0,_iG)-1|0;}}}else{return quot(_iF-1|0,_iG)-1|0;}}},_iH=new T(function(){return B(unCStr("GHC.Exception"));}),_iI=new T(function(){return B(unCStr("base"));}),_iJ=new T(function(){return B(unCStr("ArithException"));}),_iK=new T(function(){var _iL=hs_wordToWord64(4194982440),_iM=hs_wordToWord64(3110813675);return [0,_iL,_iM,[0,_iL,_iM,_iI,_iH,_iJ],_11,_11];}),_iN=function(_iO){return E(_iK);},_iP=function(_iQ){var _iR=E(_iQ);return new F(function(){return _1w(B(_1u(_iR[1])),_iN,_iR[2]);});},_iS=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_iT=new T(function(){return B(unCStr("denormal"));}),_iU=new T(function(){return B(unCStr("divide by zero"));}),_iV=new T(function(){return B(unCStr("loss of precision"));}),_iW=new T(function(){return B(unCStr("arithmetic underflow"));}),_iX=new T(function(){return B(unCStr("arithmetic overflow"));}),_iY=function(_iZ,_j0){switch(E(_iZ)){case 0:return new F(function(){return _v(_iX,_j0);});break;case 1:return new F(function(){return _v(_iW,_j0);});break;case 2:return new F(function(){return _v(_iV,_j0);});break;case 3:return new F(function(){return _v(_iU,_j0);});break;case 4:return new F(function(){return _v(_iT,_j0);});break;default:return new F(function(){return _v(_iS,_j0);});}},_j1=function(_j2){return new F(function(){return _iY(_j2,_11);});},_j3=function(_j4,_j5,_j6){return new F(function(){return _iY(_j5,_j6);});},_j7=function(_j8,_j9){return new F(function(){return _2O(_iY,_j8,_j9);});},_ja=[0,_j3,_j1,_j7],_jb=new T(function(){return [0,_iN,_ja,_jc,_iP,_j1];}),_jc=function(_jd){return [0,_jb,_jd];},_je=3,_jf=new T(function(){return B(_jc(_je));}),_jg=new T(function(){return die(_jf);}),_jh=0,_ji=new T(function(){return B(_jc(_jh));}),_jj=new T(function(){return die(_ji);}),_jk=function(_jl,_jm){var _jn=E(_jm);switch(_jn){case -1:var _jo=E(_jl);if(_jo==(-2147483648)){return E(_jj);}else{return new F(function(){return _iE(_jo,-1);});}break;case 0:return E(_jg);default:return new F(function(){return _iE(_jl,_jn);});}},_jp=new T(function(){return B(unCStr("%"));}),_jq=new T(function(){return B(unCStr("width"));}),_jr=function(_js){return E(E(_js)[1]);},_jt=function(_ju){return E(E(_ju)[2]);},_jv=function(_jw,_jx,_jy,_jz,_jA){var _jB=function(_){var _jC=jsSetStyle(B(A(_jr,[_jw,_jy])),toJSStr(E(_jz)),toJSStr(E(_jA)));return _eF;};return new F(function(){return A(_jt,[_jx,_jB]);});},_jD=function(_jE,_jF,_){while(1){var _jG=(function(_jH,_jI,_){var _jJ=E(_jH);if(!_jJ[0]){return _eF;}else{var _jK=E(_jI);if(!_jK[0]){return _eF;}else{var _jL=_jK[1],_jM=new T(function(){var _jN=E(_jL);return B(_v(B(_H(0,B(_jk(imul(E(_jN[10]),100)|0,E(_jN[9]))),_11)),_jp));}),_jO=B(A(_jv,[_4b,_4Q,_jJ[1],_jq,_jM,_]));_jE=_jJ[2];_jF=_jK[2];return null;}}})(_jE,_jF,_);if(_jG!=null){return _jG;}}},_jP=function(_jQ,_jR,_){while(1){var _jS=(function(_jT,_jU,_){var _jV=E(_jT);if(!_jV[0]){return _eF;}else{var _jW=_jV[2],_jX=E(_jU);if(!_jX[0]){return _eF;}else{var _jY=_jX[2],_jZ=E(_jX[1]),_k0=_jZ[12],_k1=E(_jZ[11]);if(!_k1){_jQ=_jW;_jR=_jY;return null;}else{var _k2=new T(function(){var _k3=E(_k0),_k4=E(_k1);if(_k4==(-1)){var _k5=imul(_k3,100)|0;if(_k5==(-2147483648)){return E(_jj);}else{return B(_v(B(_H(0,B(_iE(_k5,-1)),_11)),_jp));}}else{return B(_v(B(_H(0,B(_iE(imul(_k3,100)|0,_k4)),_11)),_jp));}}),_k6=B(A(_jv,[_4b,_4Q,_jV[1],_jq,_k2,_]));_jQ=_jW;_jR=_jY;return null;}}}})(_jQ,_jR,_);if(_jS!=null){return _jS;}}},_k7=new T(function(){return B(unCStr("innerHTML"));}),_k8=function(_k9,_ka,_kb,_kc,_kd){var _ke=function(_){var _kf=jsSet(B(A(_jr,[_k9,_kb])),toJSStr(E(_kc)),toJSStr(E(_kd)));return _eF;};return new F(function(){return A(_jt,[_ka,_ke]);});},_kg=function(_kh,_ki,_){while(1){var _kj=(function(_kk,_kl,_){var _km=E(_kk);if(!_km[0]){return _eF;}else{var _kn=E(_kl);if(!_kn[0]){return _eF;}else{var _ko=_kn[1],_kp=new T(function(){return E(E(_ko)[1]);}),_kq=B(A(_k8,[_4b,_4Q,_km[1],_k7,_kp,_]));_kh=_km[2];_ki=_kn[2];return null;}}})(_kh,_ki,_);if(_kj!=null){return _kj;}}},_kr=function(_ks,_kt,_){while(1){var _ku=(function(_kv,_kw,_){var _kx=E(_kv);if(!_kx[0]){return _eF;}else{var _ky=E(_kw);if(!_ky[0]){return _eF;}else{var _kz=_ky[1],_kA=new T(function(){var _kB=E(_kz);return B(_v(B(_H(0,B(_jk(imul(E(_kB[10]),100)|0,E(_kB[9]))),_11)),_jp));}),_kC=B(A(_jv,[_4b,_4Q,_kx[1],_jq,_kA,_]));_ks=_kx[2];_kt=_ky[2];return null;}}})(_ks,_kt,_);if(_ku!=null){return _ku;}}},_kD=new T(function(){return B(unCStr("#enemy-display-name"));}),_kE=new T(function(){return B(unCStr("#enemy-chara"));}),_kF=new T(function(){return B(unCStr("#player-chara"));}),_kG=new T(function(){return B(unCStr("#enemy-display-hpratio"));}),_kH=new T(function(){return B(unCStr("#player-display-mpratio"));}),_kI=function(_kJ){return new F(function(){return _H(0,E(E(_kJ)[11]),_11);});},_kK=new T(function(){return B(unCStr("#player-display-maxmp"));}),_kL=function(_kM){return new F(function(){return _H(0,E(E(_kM)[12]),_11);});},_kN=new T(function(){return B(unCStr("#player-display-mp"));}),_kO=new T(function(){return B(unCStr("#player-display-hpratio"));}),_kP=function(_kQ){return new F(function(){return _H(0,E(E(_kQ)[9]),_11);});},_kR=new T(function(){return B(unCStr("#player-display-maxhp"));}),_kS=function(_kT){return new F(function(){return _H(0,E(E(_kT)[10]),_11);});},_kU=new T(function(){return B(unCStr("#player-display-hp"));}),_kV=function(_kW){return E(E(_kW)[1]);},_kX=new T(function(){return B(unCStr("#player-display-name"));}),_kY=function(_kZ,_l0,_){var _l1=jsQuerySelectorAll(_kZ,toJSStr(E(_kF))),_l2=new T(function(){return E(E(_l0)[1]);}),_l3=function(_,_l4){var _l5=jsQuerySelectorAll(_kZ,toJSStr(E(_kE))),_l6=new T(function(){return E(E(_l0)[2]);});if(!_l5[0]){return _eF;}else{var _l7=E(_l5[1]),_l8=E(_kD),_l9=jsQuerySelectorAll(_l7,toJSStr(_l8)),_la=B(_kg(_l9,_l6,_)),_lb=E(_kG),_lc=jsQuerySelectorAll(_l7,toJSStr(_lb)),_ld=B(_kr(_lc,_l6,_)),_le=_l5[2],_=_;while(1){var _lf=E(_le);if(!_lf[0]){return _eF;}else{var _lg=E(_lf[1]),_lh=jsQuerySelectorAll(_lg,toJSStr(_l8)),_li=B(_kg(_lh,_l6,_)),_lj=jsQuerySelectorAll(_lg,toJSStr(_lb)),_lk=B(_kr(_lj,_l6,_));_le=_lf[2];continue;}}}};if(!_l1[0]){return new F(function(){return _l3(_,_eF);});}else{var _ll=_l1[1],_lm=function(_ln,_lo,_){var _lp=jsQuerySelectorAll(E(_ll),toJSStr(E(_ln))),_lq=_lp,_lr=_l2,_=_;while(1){var _ls=(function(_lt,_lu,_){var _lv=E(_lt);if(!_lv[0]){return _eF;}else{var _lw=E(_lu);if(!_lw[0]){return _eF;}else{var _lx=_lw[1],_ly=new T(function(){return B(A(_lo,[_lx]));}),_lz=B(A(_k8,[_4b,_4Q,_lv[1],_k7,_ly,_]));_lq=_lv[2];_lr=_lw[2];return null;}}})(_lq,_lr,_);if(_ls!=null){return _ls;}}},_lA=B(_lm(_kX,_kV,_)),_lB=B(_lm(_kU,_kS,_)),_lC=B(_lm(_kR,_kP,_)),_lD=E(_ll),_lE=E(_kO),_lF=jsQuerySelectorAll(_lD,toJSStr(_lE)),_lG=B(_jD(_lF,_l2,_)),_lH=B(_lm(_kN,_kL,_)),_lI=B(_lm(_kK,_kI,_)),_lJ=E(_kH),_lK=jsQuerySelectorAll(_lD,toJSStr(_lJ)),_lL=B(_jP(_lK,_l2,_)),_lM=function(_lN,_){while(1){var _lO=(function(_lP,_){var _lQ=E(_lP);if(!_lQ[0]){return _eF;}else{var _lR=_lQ[1],_lS=function(_lT,_lU,_){var _lV=jsQuerySelectorAll(E(_lR),toJSStr(E(_lT))),_lW=_lV,_lX=_l2,_=_;while(1){var _lY=(function(_lZ,_m0,_){var _m1=E(_lZ);if(!_m1[0]){return _eF;}else{var _m2=E(_m0);if(!_m2[0]){return _eF;}else{var _m3=_m2[1],_m4=new T(function(){return B(A(_lU,[_m3]));}),_m5=B(A(_k8,[_4b,_4Q,_m1[1],_k7,_m4,_]));_lW=_m1[2];_lX=_m2[2];return null;}}})(_lW,_lX,_);if(_lY!=null){return _lY;}}},_m6=B(_lS(_kX,_kV,_)),_m7=B(_lS(_kU,_kS,_)),_m8=B(_lS(_kR,_kP,_)),_m9=E(_lR),_ma=jsQuerySelectorAll(_m9,toJSStr(_lE)),_mb=B(_jD(_ma,_l2,_)),_mc=B(_lS(_kN,_kL,_)),_md=B(_lS(_kK,_kI,_)),_me=jsQuerySelectorAll(_m9,toJSStr(_lJ)),_mf=B(_jP(_me,_l2,_));_lN=_lQ[2];return null;}})(_lN,_);if(_lO!=null){return _lO;}}},_mg=B(_lM(_l1[2],_));return new F(function(){return _l3(_,_mg);});}},_mh=0,_mi=function(_mj){return E(E(_mj)[1]);},_mk=function(_ml){return E(E(_ml)[2]);},_mm=function(_mn){return new F(function(){return fromJSStr(E(_mn));});},_mo=function(_mp,_mq,_mr,_ms){var _mt=function(_){return new F(function(){return jsGet(B(A(_jr,[_mp,_mr])),E(_ms));});};return new F(function(){return A(_jt,[_mq,_mt]);});},_mu=function(_mv){return E(E(_mv)[4]);},_mw=function(_mx,_my,_mz,_mA){var _mB=B(_mi(_my)),_mC=new T(function(){return B(_mu(_mB));}),_mD=function(_mE){var _mF=new T(function(){return B(_mm(_mE));});return new F(function(){return A(_mC,[_mF]);});},_mG=new T(function(){var _mH=new T(function(){return toJSStr(E(_mA));});return B(_mo(_mx,_my,_mz,_mH));});return new F(function(){return A(_mk,[_mB,_mG,_mD]);});},_mI=function(_mJ,_mK,_){var _mL=B(A(_mw,[_4b,_4Q,_mJ,_k7,_])),_mM=_mL,_mN=new T(function(){return B(_v(_mM,_mK));});return new F(function(){return A(_k8,[_4b,_4Q,_mJ,_k7,_mN,_]);});},_mO=new T(function(){return B(unCStr("  <div class=\"enemy\">"));}),_mP=new T(function(){return B(unCStr("    <span id=\"enemy-display-name\"></span><br>"));}),_mQ=new T(function(){return B(unCStr("    HP"));}),_mR=new T(function(){return B(unCStr("    <div class=\"progress\">"));}),_mS=new T(function(){return B(unCStr("      <div class=\"progress-bar\" role=\"progressbar\" id=\"enemy-display-hpratio\">"));}),_mT=new T(function(){return B(unCStr("      </div>"));}),_mU=new T(function(){return B(unCStr("    </div>"));}),_mV=new T(function(){return B(unCStr("</div>"));}),_mW=[1,_mV,_11],_mX=new T(function(){return B(unCStr("  </div>"));}),_mY=[1,_mX,_mW],_mZ=[1,_mU,_mY],_n0=[1,_mT,_mZ],_n1=[1,_mS,_n0],_n2=[1,_mR,_n1],_n3=[1,_mQ,_n2],_n4=[1,_mP,_n3],_n5=[1,_mO,_n4],_n6=new T(function(){return B(unCStr("<div class=\"col-md-4\">"));}),_n7=function(_n8){var _n9=E(_n8);if(!_n9[0]){return [0];}else{var _na=_n9[2],_nb=new T(function(){return B(_n7(_na));},1);return new F(function(){return _v(_n9[1],_nb);});}},_nc=function(_nd,_ne){var _nf=new T(function(){return B(_n7(_ne));},1);return new F(function(){return _v(_nd,_nf);});},_ng=new T(function(){return B(_nc(_n6,_n5));}),_nh=new T(function(){return B(unCStr("  <div class=\"player\">"));}),_ni=new T(function(){return B(unCStr("    <span id=\"player-display-name\"></span><br>"));}),_nj=new T(function(){return B(unCStr("    HP <span id=\"player-display-hp\"></span> / <span id=\"player-display-maxhp\"></span>"));}),_nk=new T(function(){return B(unCStr("      <div class=\"progress-bar\" role=\"progressbar\" id=\"player-display-hpratio\">"));}),_nl=new T(function(){return B(unCStr("      <div class=\"progress-bar progress-bar-info\" role=\"progressbar\" id=\"player-display-mpratio\">"));}),_nm=[1,_nl,_n0],_nn=[1,_mR,_nm],_no=new T(function(){return B(unCStr("    MP <span id=\"player-display-mp\"></span> / <span id=\"player-display-maxmp\"></span>"));}),_np=[1,_no,_nn],_nq=[1,_mU,_np],_nr=[1,_mT,_nq],_ns=[1,_nk,_nr],_nt=[1,_mR,_ns],_nu=[1,_nj,_nt],_nv=[1,_ni,_nu],_nw=[1,_nh,_nv],_nx=function(_ny){var _nz=E(_ny);if(!_nz[0]){return [0];}else{var _nA=_nz[2],_nB=new T(function(){return B(_nx(_nA));},1);return new F(function(){return _v(_nz[1],_nB);});}},_nC=function(_nD,_nE){var _nF=new T(function(){return B(_nx(_nE));},1);return new F(function(){return _v(_nD,_nF);});},_nG=new T(function(){return B(_nC(_n6,_nw));}),_nH=new T(function(){return B(unCStr("#step-battle"));}),_nI=function(_nJ){var _nK=new T(function(){return B(unCStr(_nJ));});return new F(function(){return err(B(unAppCStr("Oops!  Entered absent arg ",_nK)));});},_nL=new T(function(){return B(_nI("ww_sGsX Int"));}),_nM=new T(function(){return B(_nI("ww_sGsY TacticList"));}),_nN=new T(function(){return B(unCStr("Control.Exception.Base"));}),_nO=new T(function(){return B(unCStr("base"));}),_nP=new T(function(){return B(unCStr("PatternMatchFail"));}),_nQ=new T(function(){var _nR=hs_wordToWord64(18445595),_nS=hs_wordToWord64(52003073);return [0,_nR,_nS,[0,_nR,_nS,_nO,_nN,_nP],_11,_11];}),_nT=function(_nU){return E(_nQ);},_nV=function(_nW){var _nX=E(_nW);return new F(function(){return _1w(B(_1u(_nX[1])),_nT,_nX[2]);});},_nY=function(_nZ){return E(E(_nZ)[1]);},_o0=function(_o1){return [0,_o2,_o1];},_o3=function(_o4,_o5){return new F(function(){return _v(E(_o4)[1],_o5);});},_o6=function(_o7,_o8){return new F(function(){return _2O(_o3,_o7,_o8);});},_o9=function(_oa,_ob,_oc){return new F(function(){return _v(E(_ob)[1],_oc);});},_od=[0,_o9,_nY,_o6],_o2=new T(function(){return [0,_nT,_od,_o0,_nV,_nY];}),_oe=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_of=function(_og){return E(E(_og)[3]);},_oh=function(_oi,_oj){var _ok=new T(function(){return B(A(_of,[_oj,_oi]));});return new F(function(){return die(_ok);});},_ol=function(_om,_jd){return new F(function(){return _oh(_om,_jd);});},_on=function(_oo,_op){var _oq=E(_op);if(!_oq[0]){return [0,_11,_11];}else{var _or=_oq[1],_os=_oq[2];if(!B(A(_oo,[_or]))){return [0,_11,_oq];}else{var _ot=new T(function(){var _ou=B(_on(_oo,_os));return [0,_ou[1],_ou[2]];}),_ov=new T(function(){return E(E(_ot)[2]);}),_ow=new T(function(){return E(E(_ot)[1]);});return [0,[1,_or,_ow],_ov];}}},_ox=32,_oy=new T(function(){return B(unCStr("\n"));}),_oz=function(_oA){return (E(_oA)==124)?false:true;},_oB=function(_oC,_oD){var _oE=B(_on(_oz,B(unCStr(_oC)))),_oF=_oE[1],_oG=function(_oH,_oI){var _oJ=new T(function(){var _oK=new T(function(){var _oL=new T(function(){return B(_v(_oI,_oy));},1);return B(_v(_oD,_oL));});return B(unAppCStr(": ",_oK));},1);return new F(function(){return _v(_oH,_oJ);});},_oM=E(_oE[2]);if(!_oM[0]){return new F(function(){return _oG(_oF,_11);});}else{if(E(_oM[1])==124){return new F(function(){return _oG(_oF,[1,_ox,_oM[2]]);});}else{return new F(function(){return _oG(_oF,_11);});}}},_oN=function(_oO){var _oP=new T(function(){return B(_oB(_oO,_oe));});return new F(function(){return _ol([0,_oP],_o2);});},_oQ=function(_oR){return new F(function(){return _oN("Main.hs:(273,35)-(279,30)|lambda");});},_oS=new T(function(){return B(_oQ(_));}),_oT=function(_oU){return new F(function(){return _oN("Main.hs:(267,35)-(269,41)|lambda");});},_oV=new T(function(){return B(_oT(_));}),_oW=function(_oX){return new F(function(){return _oN("Main.hs:(263,36)-(265,42)|lambda");});},_oY=new T(function(){return B(_oW(_));}),_oZ=function(_p0){return E(E(_p0)[1]);},_p1=function(_p2){return E(E(_p2)[2]);},_p3=function(_p4){return E(E(_p4)[1]);},_p5=function(_){return new F(function(){return nMV(_3c);});},_p6=new T(function(){return B(_3v(_p5));}),_p7=(function(e,name,f){e.addEventListener(name,f,false);return [f];}),_p8=function(_p9){return E(E(_p9)[2]);},_pa=function(_pb,_pc,_pd,_pe,_pf,_pg){var _ph=B(_oZ(_pb)),_pi=B(_mi(_ph)),_pj=new T(function(){return B(_jt(_ph));}),_pk=new T(function(){return B(_mu(_pi));}),_pl=new T(function(){return B(A(_jr,[_pc,_pe]));}),_pm=new T(function(){return B(A(_p3,[_pd,_pf]));}),_pn=function(_po){return new F(function(){return A(_pk,[[0,_pm,_pl,_po]]);});},_pp=function(_pq){var _pr=new T(function(){var _ps=new T(function(){var _pt=E(_pl),_pu=E(_pm),_pv=E(_pq),_pw=function(_px,_){var _py=B(A(_pv,[_px,_]));return _3z;},_pz=__createJSFunc(2,E(_pw)),_pA=_pz,_pB=function(_){return new F(function(){return E(_p7)(_pt,_pu,_pA);});};return E(_pB);});return B(A(_pj,[_ps]));});return new F(function(){return A(_mk,[_pi,_pr,_pn]);});},_pC=new T(function(){var _pD=new T(function(){return B(_jt(_ph));}),_pE=function(_pF){var _pG=new T(function(){var _pH=function(_){var _=wMV(E(_p6),[1,_pF]);return new F(function(){return A(_p1,[_pd,_pf,_pF,_]);});};return B(A(_pD,[_pH]));});return new F(function(){return A(_mk,[_pi,_pG,_pg]);});};return B(A(_p8,[_pb,_pE]));});return new F(function(){return A(_mk,[_pi,_pC,_pp]);});},_pI=function(_pJ,_pK,_pL,_){var _pM=rMV(_pK),_pN=E(_pJ),_pO=jsQuerySelectorAll(_pN,toJSStr(E(_kF))),_pP=E(E(_pM)[7]),_pQ=_pP[1],_pR=_pP[2];if(!_pO[0]){return E(_oY);}else{var _pS=_pO[1];if(!E(_pO[2])[0]){var _pT=function(_pU,_){while(1){var _pV=E(_pU);if(!_pV[0]){return _eF;}else{var _pW=B(_mI(_pS,_nG,_));_pU=_pV[2];continue;}}},_pX=B(_pT(_pQ,_)),_pY=jsQuerySelectorAll(_pN,toJSStr(E(_kE)));if(!_pY[0]){return E(_oV);}else{var _pZ=_pY[1];if(!E(_pY[2])[0]){var _q0=function(_q1,_){while(1){var _q2=E(_q1);if(!_q2[0]){return _eF;}else{var _q3=B(_mI(_pZ,_ng,_));_q1=_q2[2];continue;}}},_q4=B(_q0(_pR,_)),_q5=B(_kY(_pN,[0,_pQ,_pR,_nL,_nM],_)),_q6=jsQuerySelectorAll(_pN,toJSStr(E(_nH)));if(!_q6[0]){return E(_oS);}else{if(!E(_q6[2])[0]){var _q7=function(_q8,_){var _q9=rMV(_pK),_qa=E(_q9),_qb=E(_qa[7]),_qc=B(_ic(_qb[1],_qb[2],_qb[3],_qb[4],_)),_=wMV(_pK,[0,_qa[1],_qa[2],_qa[3],_qa[4],_qa[5],_qa[6],E(_qc)[2]]),_qd=B(A(_pL,[_])),_qe=rMV(_pK),_qf=_qe,_qg=new T(function(){return E(E(_qf)[7]);});return new F(function(){return _kY(_pN,_qg,_);});},_qh=B(A(_pa,[_4R,_4b,_46,_q6[1],_mh,_q7,_]));return _eF;}else{return E(_oS);}}}else{return E(_oV);}}}else{return E(_oY);}}},_qi=function(_qj,_qk,_ql,_qm){return (_qj!=_ql)?true:(E(_qk)!=E(_qm))?true:false;},_qn=function(_qo,_qp){var _qq=E(_qo),_qr=E(_qp);return new F(function(){return _qi(E(_qq[1]),_qq[2],E(_qr[1]),_qr[2]);});},_qs=function(_qt,_qu,_qv,_qw){if(_qt!=_qv){return false;}else{return new F(function(){return _4S(_qu,_qw);});}},_qx=function(_qy,_qz){var _qA=E(_qy),_qB=E(_qz);return new F(function(){return _qs(E(_qA[1]),_qA[2],E(_qB[1]),_qB[2]);});},_qC=[0,_qx,_qn],_qD=function(_qE,_qF,_qG,_qH){if(_qE>=_qG){if(_qE!=_qG){return 2;}else{return new F(function(){return _5c(_qF,_qH);});}}else{return 0;}},_qI=function(_qJ,_qK){var _qL=E(_qJ),_qM=E(_qK);return new F(function(){return _qD(E(_qL[1]),_qL[2],E(_qM[1]),_qM[2]);});},_qN=function(_qO,_qP,_qQ,_qR){if(_qO>=_qQ){if(_qO!=_qQ){return false;}else{return new F(function(){return _5o(_qP,_qR);});}}else{return true;}},_qS=function(_qT,_qU){var _qV=E(_qT),_qW=E(_qU);return new F(function(){return _qN(E(_qV[1]),_qV[2],E(_qW[1]),_qW[2]);});},_qX=function(_qY,_qZ,_r0,_r1){if(_qY>=_r0){if(_qY!=_r0){return false;}else{return new F(function(){return _5l(_qZ,_r1);});}}else{return true;}},_r2=function(_r3,_r4){var _r5=E(_r3),_r6=E(_r4);return new F(function(){return _qX(E(_r5[1]),_r5[2],E(_r6[1]),_r6[2]);});},_r7=function(_r8,_r9,_ra,_rb){if(_r8>=_ra){if(_r8!=_ra){return true;}else{return new F(function(){return _5i(_r9,_rb);});}}else{return false;}},_rc=function(_rd,_re){var _rf=E(_rd),_rg=E(_re);return new F(function(){return _r7(E(_rf[1]),_rf[2],E(_rg[1]),_rg[2]);});},_rh=function(_ri,_rj,_rk,_rl){if(_ri>=_rk){if(_ri!=_rk){return true;}else{return new F(function(){return _5f(_rj,_rl);});}}else{return false;}},_rm=function(_rn,_ro){var _rp=E(_rn),_rq=E(_ro);return new F(function(){return _rh(E(_rp[1]),_rp[2],E(_rq[1]),_rq[2]);});},_rr=function(_rs,_rt){var _ru=E(_rs),_rv=E(_ru[1]),_rw=E(_rt),_rx=E(_rw[1]);return (_rv>=_rx)?(_rv!=_rx)?E(_ru):(E(_ru[2])>E(_rw[2]))?E(_ru):E(_rw):E(_rw);},_ry=function(_rz,_rA){var _rB=E(_rz),_rC=E(_rB[1]),_rD=E(_rA),_rE=E(_rD[1]);return (_rC>=_rE)?(_rC!=_rE)?E(_rD):(E(_rB[2])>E(_rD[2]))?E(_rD):E(_rB):E(_rB);},_rF=[0,_qC,_qI,_qS,_r2,_rc,_rm,_rr,_ry],_rG=new T(function(){return B(unCStr("Map.!: given key is not an element in the map"));}),_rH=new T(function(){return B(err(_rG));}),_rI=function(_rJ,_rK,_rL){while(1){var _rM=E(_rL);if(!_rM[0]){var _rN=_rM[4],_rO=_rM[5],_rP=E(_rM[2]),_rQ=E(_rP[1]);if(_rJ>=_rQ){if(_rJ!=_rQ){_rL=_rO;continue;}else{var _rR=E(_rP[2]);if(_rK>=_rR){if(_rK!=_rR){_rL=_rO;continue;}else{return E(_rM[3]);}}else{_rL=_rN;continue;}}}else{_rL=_rN;continue;}}else{return E(_rH);}}},_rS=function(_rT,_rU,_rV,_){var _rW=B(A(_rU,[_rV,_])),_rX=_rW,_rY=new T(function(){return E(E(_rX)[2]);});return [0,_rT,_rY];},_rZ=function(_s0,_s1,_s2,_){var _s3=B(A(_s1,[_s2,_])),_s4=_s3,_s5=new T(function(){return E(E(_s4)[2]);}),_s6=new T(function(){var _s7=new T(function(){return E(E(_s4)[1]);});return B(A(_s0,[_s7]));});return [0,_s6,_s5];},_s8=[0,_rZ,_rS],_s9=function(_sa,_sb,_sc,_){var _sd=B(A(_sa,[_sc,_])),_se=_sd,_sf=new T(function(){return E(E(_se)[2]);}),_sg=B(A(_sb,[_sf,_])),_sh=_sg,_si=new T(function(){return E(E(_sh)[2]);}),_sj=new T(function(){var _sk=new T(function(){return E(E(_sh)[1]);});return B(A(E(_se)[1],[_sk]));});return [0,_sj,_si];},_sl=function(_sm,_sn,_so,_){var _sp=B(A(_sm,[_so,_])),_sq=_sp,_sr=new T(function(){return E(E(_sq)[2]);}),_ss=B(A(_sn,[_sr,_])),_st=_ss,_su=new T(function(){return E(E(_st)[2]);}),_sv=new T(function(){return E(E(_st)[1]);});return [0,_sv,_su];},_sw=function(_sx,_sy,_sz,_){var _sA=B(A(_sx,[_sz,_])),_sB=_sA,_sC=new T(function(){return E(E(_sB)[2]);}),_sD=B(A(_sy,[_sC,_])),_sE=_sD,_sF=new T(function(){return E(E(_sE)[2]);}),_sG=new T(function(){return E(E(_sB)[1]);});return [0,_sG,_sF];},_sH=function(_sI,_sJ,_){return [0,_sI,_sJ];},_sK=[0,_s8,_sH,_s9,_sl,_sw],_sL=function(_sM,_sN,_sO,_){var _sP=B(A(_sM,[_sO,_])),_sQ=_sP,_sR=new T(function(){return E(E(_sQ)[2]);}),_sS=new T(function(){return E(E(_sQ)[1]);});return new F(function(){return A(_sN,[_sS,_sR,_]);});},_sT=function(_sU,_sV,_){return new F(function(){return _4L(_sU,_);});},_sW=function(_sX,_sY,_sZ,_t0,_t1){var _t2=function(_t3){var _t4=new T(function(){return E(E(_t3)[2]);}),_t5=new T(function(){return E(E(_t3)[1]);});return new F(function(){return A(_t0,[_t5,_t4]);});},_t6=new T(function(){return B(A(_sZ,[_t1]));});return new F(function(){return A(_mk,[_sY,_t6,_t2]);});},_t7=function(_t8){return E(E(_t8)[5]);},_t9=function(_ta,_tb,_tc){var _td=new T(function(){return B(A(_t7,[_tb,_tc]));}),_te=function(_tf){return E(_td);};return E(_te);},_tg=function(_th,_ti){var _tj=function(_tk){return new F(function(){return _t9(_th,_ti,_tk);});},_tl=function(_tm,_tn){return new F(function(){return A(_mu,[_ti,[0,_tm,_tn]]);});},_to=function(_tp,_tk){return new F(function(){return _tq(_th,_ti,_tp,_tk);});},_tr=function(_ts,_tp,_tk){return new F(function(){return _sW(_th,_ti,_ts,_tp,_tk);});};return [0,_th,_tr,_to,_tl,_tj];},_tq=function(_tt,_tu,_tv,_tw){var _tx=function(_ty){return E(_tw);};return new F(function(){return A(_mk,[B(_tg(_tt,_tu)),_tv,_tx]);});},_tz=function(_tA,_tB){return new F(function(){return _tq(_sK,_4P,_tA,_tB);});},_tC=[0,_sK,_sL,_tz,_sH,_sT],_tD=function(_tE,_tF,_){var _tG=B(A(_tE,[_]));return [0,_tG,_tF];},_tH=[0,_tC,_tD],_tI=function(_tJ,_tK,_tL,_){while(1){var _tM=(function(_tN,_tO,_tP,_){var _tQ=E(_tN);if(!_tQ[0]){return [0,_eF,_tP];}else{var _tR=E(_tO);if(!_tR[0]){return [0,_eF,_tP];}else{var _tS=_tR[1],_tT=new T(function(){var _tU=E(_tS);return B(_v(B(_H(0,B(_jk(imul(E(_tU[10]),100)|0,E(_tU[9]))),_11)),_jp));}),_tV=B(A(_jv,[_4b,_tH,_tQ[1],_jq,_tT,_tP,_])),_tW=_tV,_tX=new T(function(){return E(E(_tW)[2]);});_tJ=_tQ[2];_tK=_tR[2];_tL=_tX;return null;}}})(_tJ,_tK,_tL,_);if(_tM!=null){return _tM;}}},_tY=function(_tZ,_u0,_u1,_){while(1){var _u2=(function(_u3,_u4,_u5,_){var _u6=E(_u3);if(!_u6[0]){return [0,_eF,_u5];}else{var _u7=_u6[2],_u8=E(_u4);if(!_u8[0]){return [0,_eF,_u5];}else{var _u9=_u8[2],_ua=E(_u8[1]),_ub=_ua[12],_uc=E(_ua[11]);if(!_uc){_tZ=_u7;_u0=_u9;var _ud=_u5;_u1=_ud;return null;}else{var _ue=new T(function(){var _uf=E(_ub),_ug=E(_uc);if(_ug==(-1)){var _uh=imul(_uf,100)|0;if(_uh==(-2147483648)){return E(_jj);}else{return B(_v(B(_H(0,B(_iE(_uh,-1)),_11)),_jp));}}else{return B(_v(B(_H(0,B(_iE(imul(_uf,100)|0,_ug)),_11)),_jp));}}),_ui=B(A(_jv,[_4b,_tH,_u6[1],_jq,_ue,_u5,_])),_uj=_ui,_uk=new T(function(){return E(E(_uj)[2]);});_tZ=_u7;_u0=_u9;_u1=_uk;return null;}}}})(_tZ,_u0,_u1,_);if(_u2!=null){return _u2;}}},_ul=function(_um,_un,_uo,_){while(1){var _up=(function(_uq,_ur,_us,_){var _ut=E(_uq);if(!_ut[0]){return [0,_eF,_us];}else{var _uu=E(_ur);if(!_uu[0]){return [0,_eF,_us];}else{var _uv=_uu[1],_uw=new T(function(){return E(E(_uv)[1]);}),_ux=B(A(_k8,[_4b,_tH,_ut[1],_k7,_uw,_us,_])),_uy=_ux,_uz=new T(function(){return E(E(_uy)[2]);});_um=_ut[2];_un=_uu[2];_uo=_uz;return null;}}})(_um,_un,_uo,_);if(_up!=null){return _up;}}},_uA=function(_uB,_uC,_uD,_){while(1){var _uE=(function(_uF,_uG,_uH,_){var _uI=E(_uF);if(!_uI[0]){return [0,_eF,_uH];}else{var _uJ=E(_uG);if(!_uJ[0]){return [0,_eF,_uH];}else{var _uK=_uJ[1],_uL=new T(function(){var _uM=E(_uK);return B(_v(B(_H(0,B(_jk(imul(E(_uM[10]),100)|0,E(_uM[9]))),_11)),_jp));}),_uN=B(A(_jv,[_4b,_tH,_uI[1],_jq,_uL,_uH,_])),_uO=_uN,_uP=new T(function(){return E(E(_uO)[2]);});_uB=_uI[2];_uC=_uJ[2];_uD=_uP;return null;}}})(_uB,_uC,_uD,_);if(_uE!=null){return _uE;}}},_uQ=function(_uR,_uS,_uT,_){var _uU=jsQuerySelectorAll(_uR,toJSStr(E(_kF))),_uV=new T(function(){return E(E(_uS)[1]);});if(!_uU[0]){var _uW=jsQuerySelectorAll(_uR,toJSStr(E(_kE))),_uX=new T(function(){return E(E(_uS)[2]);});if(!_uW[0]){return [0,_eF,_uT];}else{var _uY=E(_uW[1]),_uZ=E(_kD),_v0=jsQuerySelectorAll(_uY,toJSStr(_uZ)),_v1=B(_ul(_v0,_uX,_uT,_)),_v2=_v1,_v3=E(_kG),_v4=jsQuerySelectorAll(_uY,toJSStr(_v3)),_v5=new T(function(){return E(E(_v2)[2]);}),_v6=B(_uA(_v4,_uX,_v5,_)),_v7=_v6,_v8=function(_v9,_va,_){while(1){var _vb=(function(_vc,_vd,_){var _ve=E(_vc);if(!_ve[0]){return [0,_eF,_vd];}else{var _vf=E(_ve[1]),_vg=jsQuerySelectorAll(_vf,toJSStr(_uZ)),_vh=B(_ul(_vg,_uX,_vd,_)),_vi=_vh,_vj=jsQuerySelectorAll(_vf,toJSStr(_v3)),_vk=new T(function(){return E(E(_vi)[2]);}),_vl=B(_uA(_vj,_uX,_vk,_)),_vm=_vl,_vn=new T(function(){return E(E(_vm)[2]);});_v9=_ve[2];_va=_vn;return null;}})(_v9,_va,_);if(_vb!=null){return _vb;}}},_vo=new T(function(){return E(E(_v7)[2]);});return new F(function(){return _v8(_uW[2],_vo,_);});}}else{var _vp=_uU[1],_vq=function(_vr,_vs,_vt,_){var _vu=jsQuerySelectorAll(E(_vp),toJSStr(E(_vr))),_vv=_vu,_vw=_uV,_vx=_vt,_=_;while(1){var _vy=(function(_vz,_vA,_vB,_){var _vC=E(_vz);if(!_vC[0]){return [0,_eF,_vB];}else{var _vD=E(_vA);if(!_vD[0]){return [0,_eF,_vB];}else{var _vE=_vD[1],_vF=new T(function(){return B(A(_vs,[_vE]));}),_vG=B(A(_k8,[_4b,_tH,_vC[1],_k7,_vF,_vB,_])),_vH=_vG,_vI=new T(function(){return E(E(_vH)[2]);});_vv=_vC[2];_vw=_vD[2];_vx=_vI;return null;}}})(_vv,_vw,_vx,_);if(_vy!=null){return _vy;}}},_vJ=B(_vq(_kX,_kV,_uT,_)),_vK=_vJ,_vL=new T(function(){return E(E(_vK)[2]);}),_vM=B(_vq(_kU,_kS,_vL,_)),_vN=_vM,_vO=new T(function(){return E(E(_vN)[2]);}),_vP=B(_vq(_kR,_kP,_vO,_)),_vQ=_vP,_vR=E(_vp),_vS=E(_kO),_vT=jsQuerySelectorAll(_vR,toJSStr(_vS)),_vU=new T(function(){return E(E(_vQ)[2]);}),_vV=B(_tI(_vT,_uV,_vU,_)),_vW=_vV,_vX=new T(function(){return E(E(_vW)[2]);}),_vY=B(_vq(_kN,_kL,_vX,_)),_vZ=_vY,_w0=new T(function(){return E(E(_vZ)[2]);}),_w1=B(_vq(_kK,_kI,_w0,_)),_w2=_w1,_w3=E(_kH),_w4=jsQuerySelectorAll(_vR,toJSStr(_w3)),_w5=new T(function(){return E(E(_w2)[2]);}),_w6=B(_tY(_w4,_uV,_w5,_)),_w7=_w6,_w8=function(_w9,_wa,_){while(1){var _wb=(function(_wc,_wd,_){var _we=E(_wc);if(!_we[0]){return [0,_eF,_wd];}else{var _wf=_we[1],_wg=function(_wh,_wi,_wj,_){var _wk=jsQuerySelectorAll(E(_wf),toJSStr(E(_wh))),_wl=_wk,_wm=_uV,_wn=_wj,_=_;while(1){var _wo=(function(_wp,_wq,_wr,_){var _ws=E(_wp);if(!_ws[0]){return [0,_eF,_wr];}else{var _wt=E(_wq);if(!_wt[0]){return [0,_eF,_wr];}else{var _wu=_wt[1],_wv=new T(function(){return B(A(_wi,[_wu]));}),_ww=B(A(_k8,[_4b,_tH,_ws[1],_k7,_wv,_wr,_])),_wx=_ww,_wy=new T(function(){return E(E(_wx)[2]);});_wl=_ws[2];_wm=_wt[2];_wn=_wy;return null;}}})(_wl,_wm,_wn,_);if(_wo!=null){return _wo;}}},_wz=B(_wg(_kX,_kV,_wd,_)),_wA=_wz,_wB=new T(function(){return E(E(_wA)[2]);}),_wC=B(_wg(_kU,_kS,_wB,_)),_wD=_wC,_wE=new T(function(){return E(E(_wD)[2]);}),_wF=B(_wg(_kR,_kP,_wE,_)),_wG=_wF,_wH=E(_wf),_wI=jsQuerySelectorAll(_wH,toJSStr(_vS)),_wJ=new T(function(){return E(E(_wG)[2]);}),_wK=B(_tI(_wI,_uV,_wJ,_)),_wL=_wK,_wM=new T(function(){return E(E(_wL)[2]);}),_wN=B(_wg(_kN,_kL,_wM,_)),_wO=_wN,_wP=new T(function(){return E(E(_wO)[2]);}),_wQ=B(_wg(_kK,_kI,_wP,_)),_wR=_wQ,_wS=jsQuerySelectorAll(_wH,toJSStr(_w3)),_wT=new T(function(){return E(E(_wR)[2]);}),_wU=B(_tY(_wS,_uV,_wT,_)),_wV=_wU,_wW=new T(function(){return E(E(_wV)[2]);});_w9=_we[2];_wa=_wW;return null;}})(_w9,_wa,_);if(_wb!=null){return _wb;}}},_wX=new T(function(){return E(E(_w7)[2]);}),_wY=B(_w8(_uU[2],_wX,_)),_wZ=_wY,_x0=jsQuerySelectorAll(_uR,toJSStr(E(_kE))),_x1=new T(function(){return E(E(_uS)[2]);});if(!_x0[0]){var _x2=new T(function(){return E(E(_wZ)[2]);});return [0,_eF,_x2];}else{var _x3=E(_x0[1]),_x4=E(_kD),_x5=jsQuerySelectorAll(_x3,toJSStr(_x4)),_x6=new T(function(){return E(E(_wZ)[2]);}),_x7=B(_ul(_x5,_x1,_x6,_)),_x8=_x7,_x9=E(_kG),_xa=jsQuerySelectorAll(_x3,toJSStr(_x9)),_xb=new T(function(){return E(E(_x8)[2]);}),_xc=B(_uA(_xa,_x1,_xb,_)),_xd=_xc,_xe=function(_xf,_xg,_){while(1){var _xh=(function(_xi,_xj,_){var _xk=E(_xi);if(!_xk[0]){return [0,_eF,_xj];}else{var _xl=E(_xk[1]),_xm=jsQuerySelectorAll(_xl,toJSStr(_x4)),_xn=B(_ul(_xm,_x1,_xj,_)),_xo=_xn,_xp=jsQuerySelectorAll(_xl,toJSStr(_x9)),_xq=new T(function(){return E(E(_xo)[2]);}),_xr=B(_uA(_xp,_x1,_xq,_)),_xs=_xr,_xt=new T(function(){return E(E(_xs)[2]);});_xf=_xk[2];_xg=_xt;return null;}})(_xf,_xg,_);if(_xh!=null){return _xh;}}},_xu=new T(function(){return E(E(_xd)[2]);});return new F(function(){return _xe(_x0[2],_xu,_);});}}},_xv=function(_xw,_xx,_xy,_){var _xz=B(A(_mw,[_4b,_tH,_xw,_k7,_xy,_])),_xA=_xz,_xB=new T(function(){return E(E(_xA)[2]);}),_xC=new T(function(){return B(_v(E(_xA)[1],_xx));});return new F(function(){return A(_k8,[_4b,_tH,_xw,_k7,_xC,_xB,_]);});},_xD=new T(function(){return B(_nI("ww_sGvQ Int"));}),_xE=new T(function(){return B(_nI("ww_sGvR TacticList"));}),_xF=function(_xG){return new F(function(){return _oN("Main.hs:(273,35)-(279,30)|lambda");});},_xH=new T(function(){return B(_xF(_));}),_xI=function(_xJ){return new F(function(){return _oN("Main.hs:(267,35)-(269,41)|lambda");});},_xK=new T(function(){return B(_xI(_));}),_xL=function(_xM){return new F(function(){return _oN("Main.hs:(263,36)-(265,42)|lambda");});},_xN=new T(function(){return B(_xL(_));}),_xO=function(_xP,_xQ,_xR,_xS,_){var _xT=rMV(_xQ),_xU=E(_xP),_xV=jsQuerySelectorAll(_xU,toJSStr(E(_kF))),_xW=E(E(_xT)[7]),_xX=_xW[1],_xY=_xW[2];if(!_xV[0]){return E(_xN);}else{var _xZ=_xV[1];if(!E(_xV[2])[0]){var _y0=function(_y1,_y2,_){while(1){var _y3=(function(_y4,_y5,_){var _y6=E(_y4);if(!_y6[0]){return [0,_eF,_y5];}else{var _y7=B(_xv(_xZ,_nG,_y5,_)),_y8=_y7,_y9=new T(function(){return E(E(_y8)[2]);});_y1=_y6[2];_y2=_y9;return null;}})(_y1,_y2,_);if(_y3!=null){return _y3;}}},_ya=B(_y0(_xX,_xS,_)),_yb=_ya,_yc=jsQuerySelectorAll(_xU,toJSStr(E(_kE)));if(!_yc[0]){return E(_xK);}else{var _yd=_yc[1];if(!E(_yc[2])[0]){var _ye=function(_yf,_yg,_){while(1){var _yh=(function(_yi,_yj,_){var _yk=E(_yi);if(!_yk[0]){return [0,_eF,_yj];}else{var _yl=B(_xv(_yd,_ng,_yj,_)),_ym=_yl,_yn=new T(function(){return E(E(_ym)[2]);});_yf=_yk[2];_yg=_yn;return null;}})(_yf,_yg,_);if(_yh!=null){return _yh;}}},_yo=new T(function(){return E(E(_yb)[2]);}),_yp=B(_ye(_xY,_yo,_)),_yq=_yp,_yr=new T(function(){return E(E(_yq)[2]);}),_ys=B(_uQ(_xU,[0,_xX,_xY,_xD,_xE],_yr,_)),_yt=_ys,_yu=jsQuerySelectorAll(_xU,toJSStr(E(_nH)));if(!_yu[0]){return E(_xH);}else{if(!E(_yu[2])[0]){var _yv=function(_yw,_){var _yx=rMV(_xQ),_yy=E(_yx),_yz=E(_yy[7]),_yA=B(_ic(_yz[1],_yz[2],_yz[3],_yz[4],_)),_=wMV(_xQ,[0,_yy[1],_yy[2],_yy[3],_yy[4],_yy[5],_yy[6],E(_yA)[2]]),_yB=B(A(_xR,[_])),_yC=rMV(_xQ),_yD=_yC,_yE=new T(function(){return E(E(_yD)[7]);});return new F(function(){return _kY(_xU,_yE,_);});},_yF=B(A(_pa,[_4R,_4b,_46,_yu[1],_mh,_yv,_])),_yG=new T(function(){return E(E(_yt)[2]);});return [0,_eF,_yG];}else{return E(_xH);}}}else{return E(_xK);}}}else{return E(_xN);}}},_yH=function(_){return new F(function(){return _oN("Main.hs:(367,70)-(369,40)|lambda");});},_yI=function(_yJ,_yK,_yL){while(1){var _yM=E(_yL);if(!_yM[0]){var _yN=_yM[4],_yO=_yM[5],_yP=E(_yM[2]),_yQ=E(_yP[1]);if(_yJ>=_yQ){if(_yJ!=_yQ){_yL=_yO;continue;}else{var _yR=E(_yK),_yS=E(_yP[2]);if(_yR>=_yS){if(_yR!=_yS){_yK=_yR;_yL=_yO;continue;}else{return E(_yM[3]);}}else{_yK=_yR;_yL=_yN;continue;}}}else{_yL=_yN;continue;}}else{return E(_rH);}}},_yT=new T(function(){return B(unCStr("@"));}),_yU=new T(function(){return B(unCStr("&nbsp;"));}),_yV=new T(function(){return B(_v(_yU,_yT));}),_yW=function(_yX){var _yY=E(_yX);if(_yY==1){return E(_yV);}else{var _yZ=new T(function(){return B(_yW(_yY-1|0));},1);return new F(function(){return _v(_yU,_yZ);});}},_z0="dungeon-field",_z1="dungeon-battle",_z2=function(_z3,_){while(1){var _z4=E(_z3);if(!_z4[0]){return _eF;}else{var _z5=B(A(_k8,[_4b,_4Q,_z4[1],_k7,_11,_]));_z3=_z4[2];continue;}}},_z6=function(_z7,_){while(1){var _z8=E(_z7);if(!_z8[0]){return _eF;}else{var _z9=B(A(_k8,[_4b,_4Q,_z8[1],_k7,_11,_]));_z7=_z8[2];continue;}}},_za=0,_zb=new T(function(){return document;}),_zc=function(){ $('#tabs a[href="#dungeon-battle"]').tab('show'); },_zd=function(){ $('#tabs a[href="#dungeon"]').tab('show'); },_ze=(function(e){return e.parentNode;}),_zf=function(_zg){while(1){var _zh=E(_zg);if(!_zh[0]){return true;}else{if(E(_zh[1])>0){return false;}else{_zg=_zh[2];continue;}}}},_zi=new T(function(){return B(unCStr("<br>"));}),_zj=function(_zk,_zl){if(_zk<=_zl){var _zm=function(_zn){var _zo=new T(function(){if(_zn!=_zl){return B(_zm(_zn+1|0));}else{return [0];}});return [1,_zn,_zo];};return new F(function(){return _zm(_zk);});}else{return [0];}},_zp=new T(function(){return B(_zj(0,34));}),_zq=new T(function(){return B(_zj(0,44));}),_zr=function(_zs){var _zt=E(_zs);if(!_zt[0]){return [0];}else{var _zu=_zt[2],_zv=E(_zt[1]);if(E(_zv)==32){var _zw=new T(function(){return B(_zr(_zu));},1);return new F(function(){return _v(_yU,_zw);});}else{var _zx=new T(function(){return B(_zr(_zu));},1);return new F(function(){return _v([1,_zv,_11],_zx);});}}},_zy=function(_zz){var _zA=E(_zz);if(!_zA[0]){return [0];}else{var _zB=_zA[2],_zC=new T(function(){return B(_zy(_zB));},1);return new F(function(){return _v(_zA[1],_zC);});}},_zD=function(_zE,_zF){var _zG=E(_zF);if(!_zG[0]){return [0];}else{var _zH=_zG[1],_zI=_zG[2],_zJ=new T(function(){return B(_zD(_zE,_zI));}),_zK=new T(function(){return B(A(_zE,[_zH]));});return [1,_zK,_zJ];}},_zL=function(_zM,_zN){var _zO=E(_zN);if(!_zO[0]){return [0];}else{var _zP=_zO[2],_zQ=new T(function(){return B(_zL(_zM,_zP));});return [1,_zM,[1,_zO[1],_zQ]];}},_zR=function(_zS){var _zT=function(_zU){var _zV=function(_zW,_zX){var _zY=E(_zW);if(!_zY[0]){return [0];}else{var _zZ=_zY[1],_A0=_zY[2],_A1=E(_zX);if(_A1==1){var _A2=new T(function(){return B(_yI(E(_zZ),_zU,_zS));});return [1,_A2,_11];}else{var _A3=new T(function(){return B(_zV(_A0,_A1-1|0));}),_A4=new T(function(){return B(_yI(E(_zZ),_zU,_zS));});return [1,_A4,_A3];}}};return new F(function(){return _zV(_zq,45);});},_A5=B(_zD(_zT,_zp));if(!_A5[0]){return [0];}else{var _A6=_A5[2],_A7=new T(function(){return B(_zL(_zi,_A6));});return new F(function(){return _zr(B(_zy([1,_A5[1],_A7])));});}},_A8=function(_A9){return E(E(_A9)[2]);},_Aa=function(_Ab,_Ac,_Ad,_Ae){var _Af=E(_Ac),_Ag=E(_Ae);if(!_Ag[0]){var _Ah=_Ag[2],_Ai=_Ag[3],_Aj=_Ag[4],_Ak=_Ag[5];switch(B(A(_A8,[_Ab,_Af,_Ah]))){case 0:return new F(function(){return _6x(_Ah,_Ai,B(_Aa(_Ab,_Af,_Ad,_Aj)),_Ak);});break;case 1:return [0,_Ag[1],E(_Af),_Ad,E(_Aj),E(_Ak)];default:return new F(function(){return _5E(_Ah,_Ai,_Aj,B(_Aa(_Ab,_Af,_Ad,_Ak)));});}}else{return [0,1,E(_Af),_Ad,E(_5z),E(_5z)];}},_Al=function(_Am,_An,_Ao,_Ap){return new F(function(){return _Aa(_Am,_An,_Ao,_Ap);});},_Aq=function(_Ar,_As,_At){var _Au=function(_Av){var _Aw=E(_Av);if(!_Aw[0]){return E(_At);}else{var _Ax=E(_Aw[1]);return new F(function(){return _Al(_Ar,_Ax[1],_Ax[2],B(_Au(_Aw[2])));});}};return new F(function(){return _Au(_As);});},_Ay=[1,_11,_11],_Az=function(_AA){var _AB=E(_AA);if(!_AB[0]){return E(_Ay);}else{var _AC=_AB[2],_AD=new T(function(){return B(_Az(_AC));}),_AE=function(_AF){var _AG=E(_AF);if(!_AG[0]){return [0];}else{var _AH=_AG[1],_AI=_AG[2],_AJ=new T(function(){return B(_AE(_AI));}),_AK=function(_AL){var _AM=E(_AL);if(!_AM[0]){return E(_AJ);}else{var _AN=_AM[2],_AO=new T(function(){return B(_AK(_AN));});return [1,[1,_AH,_AM[1]],_AO];}};return new F(function(){return _AK(_AD);});}};return new F(function(){return _AE(_AB[1]);});}},_AP=function(_AQ,_AR){if(0>=_AQ){return E(_Ay);}else{var _AS=[1,_AR,_11],_AT=function(_AU){var _AV=E(_AU);if(_AV==1){return E(_AS);}else{var _AW=new T(function(){return B(_AT(_AV-1|0));});return [1,_AR,_AW];}};return new F(function(){return _Az(B(_AT(_AQ)));});}},_AX=-2,_AY=-1,_AZ=1,_B0=2,_B1=[1,_B0,_11],_B2=[1,_AZ,_B1],_B3=[1,_za,_B2],_B4=[1,_AY,_B3],_B5=[1,_AX,_B4],_B6=new T(function(){return B(_AP(2,_B5));}),_B7=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:345:3-9"));}),_B8=[0,_3c,_3d,_11,_B7,_3c,_3c],_B9=new T(function(){return B(_3a(_B8));}),_Ba=new T(function(){return B(unCStr("none"));}),_Bb=new T(function(){return B(unCStr("#tabs a[href=\"#dungeon-battle\"]"));}),_Bc=new T(function(){return B(unCStr("player"));}),_Bd=function(_Be){return E(E(_Be)[10]);},_Bf=new T(function(){return B(unCStr("block"));}),_Bg=new T(function(){return B(unCStr("display"));}),_Bh=function(_Bi){return new F(function(){return _oN("Main.hs:(357,64)-(359,35)|lambda");});},_Bj=new T(function(){return B(_Bh(_));}),_Bk=new T(function(){return B(unCStr(" found!"));}),_Bl=function(_Bm){var _Bn=new T(function(){return B(_v(fromJSStr(E(_Bm)),_Bk));});return new F(function(){return err(B(unAppCStr("No element with ID ",_Bn)));});},_Bo=function(_Bp,_Bq,_Br,_Bs,_Bt,_Bu,_Bv,_){var _Bw=E(_Br),_Bx=_Bw[1],_By=_Bw[2],_Bz=function(_,_BA,_BB,_BC,_BD,_BE,_BF,_BG,_BH){var _BI=function(_,_BJ,_BK,_BL,_BM,_BN,_BO,_BP,_BQ){var _BR=function(_,_BS,_BT,_BU,_BV,_BW,_BX,_BY,_BZ){var _C0=function(_,_C1,_C2,_C3,_C4,_C5,_C6,_C7,_C8){var _C9=jsFind(toJSStr(E(_Bc)));if(!_C9[0]){return new F(function(){return die(_B9);});}else{var _Ca=new T(function(){var _Cb=function(_Cc){while(1){var _Cd=(function(_Ce){var _Cf=E(_Ce);if(!_Cf[0]){return [0];}else{var _Cg=_Cf[2],_Ch=E(_Cf[1]);if(!_Ch[0]){_Cc=_Cg;return null;}else{var _Ci=E(_Ch[2]);if(!_Ci[0]){_Cc=_Cg;return null;}else{if(!E(_Ci[2])[0]){var _Cj=E(_C2),_Ck=E(_Ch[1]);if(0>(_Cj+_Ck|0)){var _Cl=function(_Cm){while(1){var _Cn=(function(_Co){var _Cp=E(_Co);if(!_Cp[0]){return [0];}else{var _Cq=_Cp[2],_Cr=E(_Cp[1]);if(!_Cr[0]){_Cm=_Cq;return null;}else{var _Cs=E(_Cr[2]);if(!_Cs[0]){_Cm=_Cq;return null;}else{if(!E(_Cs[2])[0]){var _Ct=E(_Cr[1]);if(0>(_Cj+_Ct|0)){_Cm=_Cq;return null;}else{if((_Cj+_Ct|0)>44){_Cm=_Cq;return null;}else{var _Cu=E(_C3),_Cv=E(_Cs[1]);if(0>(_Cu+_Cv|0)){_Cm=_Cq;return null;}else{if((_Cu+_Cv|0)>34){_Cm=_Cq;return null;}else{var _Cw=new T(function(){return B(_Cl(_Cq));}),_Cx=_Cj+_Ct|0,_Cy=_Cu+_Cv|0,_Cz=new T(function(){return B(_rI(_Cx,_Cy,_C5));});return [1,[0,[0,_Cx,_Cy],_Cz],_Cw];}}}}}else{_Cm=_Cq;return null;}}}}})(_Cm);if(_Cn!=null){return _Cn;}}};return new F(function(){return _Cl(_Cg);});}else{if((_Cj+_Ck|0)>44){var _CA=function(_CB){while(1){var _CC=(function(_CD){var _CE=E(_CD);if(!_CE[0]){return [0];}else{var _CF=_CE[2],_CG=E(_CE[1]);if(!_CG[0]){_CB=_CF;return null;}else{var _CH=E(_CG[2]);if(!_CH[0]){_CB=_CF;return null;}else{if(!E(_CH[2])[0]){var _CI=E(_CG[1]);if(0>(_Cj+_CI|0)){_CB=_CF;return null;}else{if((_Cj+_CI|0)>44){_CB=_CF;return null;}else{var _CJ=E(_C3),_CK=E(_CH[1]);if(0>(_CJ+_CK|0)){_CB=_CF;return null;}else{if((_CJ+_CK|0)>34){_CB=_CF;return null;}else{var _CL=new T(function(){return B(_CA(_CF));}),_CM=_Cj+_CI|0,_CN=_CJ+_CK|0,_CO=new T(function(){return B(_rI(_CM,_CN,_C5));});return [1,[0,[0,_CM,_CN],_CO],_CL];}}}}}else{_CB=_CF;return null;}}}}})(_CB);if(_CC!=null){return _CC;}}};return new F(function(){return _CA(_Cg);});}else{var _CP=E(_C3),_CQ=E(_Ci[1]);if(0>(_CP+_CQ|0)){var _CR=function(_CS){while(1){var _CT=(function(_CU){var _CV=E(_CU);if(!_CV[0]){return [0];}else{var _CW=_CV[2],_CX=E(_CV[1]);if(!_CX[0]){_CS=_CW;return null;}else{var _CY=E(_CX[2]);if(!_CY[0]){_CS=_CW;return null;}else{if(!E(_CY[2])[0]){var _CZ=E(_CX[1]);if(0>(_Cj+_CZ|0)){_CS=_CW;return null;}else{if((_Cj+_CZ|0)>44){_CS=_CW;return null;}else{var _D0=E(_CY[1]);if(0>(_CP+_D0|0)){_CS=_CW;return null;}else{if((_CP+_D0|0)>34){_CS=_CW;return null;}else{var _D1=new T(function(){return B(_CR(_CW));}),_D2=_Cj+_CZ|0,_D3=_CP+_D0|0,_D4=new T(function(){return B(_rI(_D2,_D3,_C5));});return [1,[0,[0,_D2,_D3],_D4],_D1];}}}}}else{_CS=_CW;return null;}}}}})(_CS);if(_CT!=null){return _CT;}}};return new F(function(){return _CR(_Cg);});}else{if((_CP+_CQ|0)>34){var _D5=function(_D6){while(1){var _D7=(function(_D8){var _D9=E(_D8);if(!_D9[0]){return [0];}else{var _Da=_D9[2],_Db=E(_D9[1]);if(!_Db[0]){_D6=_Da;return null;}else{var _Dc=E(_Db[2]);if(!_Dc[0]){_D6=_Da;return null;}else{if(!E(_Dc[2])[0]){var _Dd=E(_Db[1]);if(0>(_Cj+_Dd|0)){_D6=_Da;return null;}else{if((_Cj+_Dd|0)>44){_D6=_Da;return null;}else{var _De=E(_Dc[1]);if(0>(_CP+_De|0)){_D6=_Da;return null;}else{if((_CP+_De|0)>34){_D6=_Da;return null;}else{var _Df=new T(function(){return B(_D5(_Da));}),_Dg=_Cj+_Dd|0,_Dh=_CP+_De|0,_Di=new T(function(){return B(_rI(_Dg,_Dh,_C5));});return [1,[0,[0,_Dg,_Dh],_Di],_Df];}}}}}else{_D6=_Da;return null;}}}}})(_D6);if(_D7!=null){return _D7;}}};return new F(function(){return _D5(_Cg);});}else{var _Dj=new T(function(){var _Dk=function(_Dl){while(1){var _Dm=(function(_Dn){var _Do=E(_Dn);if(!_Do[0]){return [0];}else{var _Dp=_Do[2],_Dq=E(_Do[1]);if(!_Dq[0]){_Dl=_Dp;return null;}else{var _Dr=E(_Dq[2]);if(!_Dr[0]){_Dl=_Dp;return null;}else{if(!E(_Dr[2])[0]){var _Ds=E(_Dq[1]);if(0>(_Cj+_Ds|0)){_Dl=_Dp;return null;}else{if((_Cj+_Ds|0)>44){_Dl=_Dp;return null;}else{var _Dt=E(_Dr[1]);if(0>(_CP+_Dt|0)){_Dl=_Dp;return null;}else{if((_CP+_Dt|0)>34){_Dl=_Dp;return null;}else{var _Du=new T(function(){return B(_Dk(_Dp));}),_Dv=_Cj+_Ds|0,_Dw=_CP+_Dt|0,_Dx=new T(function(){return B(_rI(_Dv,_Dw,_C5));});return [1,[0,[0,_Dv,_Dw],_Dx],_Du];}}}}}else{_Dl=_Dp;return null;}}}}})(_Dl);if(_Dm!=null){return _Dm;}}};return B(_Dk(_Cg));}),_Dy=_Cj+_Ck|0,_Dz=_CP+_CQ|0,_DA=new T(function(){return B(_rI(_Dy,_Dz,_C5));});return [1,[0,[0,_Dy,_Dz],_DA],_Dj];}}}}}else{_Cc=_Cg;return null;}}}}})(_Cc);if(_Cd!=null){return _Cd;}}};return B(_Aq(_rF,B(_Cb(_B6)),_C6));}),_DB=new T(function(){var _DC=E(_C3);if(0>=_DC){var _DD=E(_C2);if(0>=_DD){return E(_yT);}else{return B(_yW(_DD));}}else{var _DE=new T(function(){var _DF=new T(function(){var _DG=E(_C2);if(0>=_DG){return E(_yT);}else{return B(_yW(_DG));}},1);return B(_v(_zi,_DF));}),_DH=function(_DI){var _DJ=E(_DI);if(_DJ==1){return E(_DE);}else{var _DK=new T(function(){return B(_DH(_DJ-1|0));},1);return new F(function(){return _v(_zi,_DK);});}};return B(_DH(_DC));}}),_DL=B(A(_k8,[_4b,_tH,_C9[1],_k7,_DB,[0,_C1,[0,_C2,_C3],_C4,_C5,_Ca,_C7,_C8],_])),_DM=_DL,_DN=E(_z0),_DO=jsFind(_DN);if(!_DO[0]){return new F(function(){return _Bl(_DN);});}else{var _DP=new T(function(){return E(E(_DM)[2]);}),_DQ=new T(function(){var _DR=new T(function(){return E(E(_DP)[5]);});return B(_zR(_DR));}),_DS=B(A(_k8,[_4b,_tH,_DO[1],_k7,_DQ,_DP,_])),_DT=E(E(_DS)[2]);if(E(_DT[6])==5){var _DU=E(_3z),_DV=E(_zc)(_DU),_DW=E(_zb),_DX=toJSStr(E(_Bb)),_DY=jsQuerySelectorAll(_DW,_DX);if(!_DY[0]){return E(_Bj);}else{if(!E(_DY[2])[0]){var _DZ=E(_ze),_E0=_DZ(E(_DY[1])),_E1=B(A(_jv,[_4b,_tH,_E0,_Bg,_Bf,[0,_DT[1],_DT[2],_DT[3],_DT[4],_DT[5],_za,_DT[7]],_])),_E2=_E1,_E3=E(_z1),_E4=jsFind(_E3);if(!_E4[0]){return new F(function(){return _Bl(_E3);});}else{var _E5=_E4[1],_E6=E(_Bp),_E7=new T(function(){return E(E(_E2)[2]);}),_E8=function(_){var _E9=rMV(_E6);if(!B(_zf(B(_zD(_Bd,E(E(_E9)[7])[2]))))){return _eF;}else{var _Ea=E(_zd)(_DU),_Eb=jsQuerySelectorAll(_DW,_DX);if(!_Eb[0]){return new F(function(){return _yH(_);});}else{if(!E(_Eb[2])[0]){var _Ec=_DZ(E(_Eb[1])),_Ed=B(A(_jv,[_4b,_4Q,_Ec,_Bg,_Ba,_])),_Ee=E(_E5),_Ef=jsQuerySelectorAll(_Ee,toJSStr(E(_kF))),_Eg=B(_z2(_Ef,_)),_Eh=jsQuerySelectorAll(_Ee,toJSStr(E(_kE)));return new F(function(){return _z6(_Eh,_);});}else{return new F(function(){return _yH(_);});}}}};return new F(function(){return _xO(_E5,_E6,_E8,_E7,_);});}}else{return E(_Bj);}}}else{return [0,_eF,_DT];}}}};if(!B(_eY(_Bq,39))){return new F(function(){return _C0(_,_BS,_BT,_BU,_BV,_BW,_BX,_BY,_BZ);});}else{var _Ei=E(_BT),_Ej=_Ei+1|0;switch(E(B(_yI(_Ej,_BU,_BW)))){case 35:var _Ek=new T(function(){return E(_BY)+1|0;});return new F(function(){return _C0(_,_BS,_Ej,_BU,_BV,_BW,_BX,_Ek,_BZ);});break;case 45:var _El=new T(function(){return E(_BY)+1|0;});return new F(function(){return _C0(_,_BS,_Ej,_BU,_BV,_BW,_BX,_El,_BZ);});break;default:return new F(function(){return _C0(_,_BS,_Ei,_BU,_BV,_BW,_BX,_BY,_BZ);});}}};if(!B(_eY(_Bq,37))){return new F(function(){return _BR(_,_BJ,_BK,_BL,_BM,_BN,_BO,_BP,_BQ);});}else{var _Em=_BK+(-1)|0;switch(E(B(_yI(_Em,_BL,_BN)))){case 35:var _En=new T(function(){return E(_BP)+1|0;});return new F(function(){return _BR(_,_BJ,_Em,_BL,_BM,_BN,_BO,_En,_BQ);});break;case 45:var _Eo=new T(function(){return E(_BP)+1|0;});return new F(function(){return _BR(_,_BJ,_Em,_BL,_BM,_BN,_BO,_Eo,_BQ);});break;default:return new F(function(){return _BR(_,_BJ,_BK,_BL,_BM,_BN,_BO,_BP,_BQ);});}}};if(!B(_eY(_Bq,40))){return new F(function(){return _BI(_,_BA,_BB,_BC,_BD,_BE,_BF,_BG,_BH);});}else{var _Ep=new T(function(){return E(_BC)+1|0;});switch(E(B(_yI(_BB,_Ep,_BE)))){case 35:var _Eq=new T(function(){return E(_BG)+1|0;});return new F(function(){return _BI(_,_BA,_BB,_Ep,_BD,_BE,_BF,_Eq,_BH);});break;case 45:var _Er=new T(function(){return E(_BG)+1|0;});return new F(function(){return _BI(_,_BA,_BB,_Ep,_BD,_BE,_BF,_Er,_BH);});break;default:return new F(function(){return _BI(_,_BA,_BB,_BC,_BD,_BE,_BF,_BG,_BH);});}}};if(!B(_eY(_Bq,38))){var _Es=function(_,_Et,_Eu,_Ev,_Ew,_Ex,_Ey,_Ez,_EA){var _EB=function(_,_EC,_ED,_EE,_EF,_EG,_EH,_EI,_EJ){var _EK=function(_,_EL,_EM,_EN,_EO,_EP,_EQ,_ER,_ES){var _ET=jsFind(toJSStr(E(_Bc)));if(!_ET[0]){return new F(function(){return die(_B9);});}else{var _EU=new T(function(){var _EV=function(_EW){while(1){var _EX=(function(_EY){var _EZ=E(_EY);if(!_EZ[0]){return [0];}else{var _F0=_EZ[2],_F1=E(_EZ[1]);if(!_F1[0]){_EW=_F0;return null;}else{var _F2=E(_F1[2]);if(!_F2[0]){_EW=_F0;return null;}else{if(!E(_F2[2])[0]){var _F3=E(_EM),_F4=E(_F1[1]);if(0>(_F3+_F4|0)){var _F5=function(_F6){while(1){var _F7=(function(_F8){var _F9=E(_F8);if(!_F9[0]){return [0];}else{var _Fa=_F9[2],_Fb=E(_F9[1]);if(!_Fb[0]){_F6=_Fa;return null;}else{var _Fc=E(_Fb[2]);if(!_Fc[0]){_F6=_Fa;return null;}else{if(!E(_Fc[2])[0]){var _Fd=E(_Fb[1]);if(0>(_F3+_Fd|0)){_F6=_Fa;return null;}else{if((_F3+_Fd|0)>44){_F6=_Fa;return null;}else{var _Fe=E(_EN),_Ff=E(_Fc[1]);if(0>(_Fe+_Ff|0)){_F6=_Fa;return null;}else{if((_Fe+_Ff|0)>34){_F6=_Fa;return null;}else{var _Fg=new T(function(){return B(_F5(_Fa));}),_Fh=_F3+_Fd|0,_Fi=_Fe+_Ff|0,_Fj=new T(function(){return B(_rI(_Fh,_Fi,_EP));});return [1,[0,[0,_Fh,_Fi],_Fj],_Fg];}}}}}else{_F6=_Fa;return null;}}}}})(_F6);if(_F7!=null){return _F7;}}};return new F(function(){return _F5(_F0);});}else{if((_F3+_F4|0)>44){var _Fk=function(_Fl){while(1){var _Fm=(function(_Fn){var _Fo=E(_Fn);if(!_Fo[0]){return [0];}else{var _Fp=_Fo[2],_Fq=E(_Fo[1]);if(!_Fq[0]){_Fl=_Fp;return null;}else{var _Fr=E(_Fq[2]);if(!_Fr[0]){_Fl=_Fp;return null;}else{if(!E(_Fr[2])[0]){var _Fs=E(_Fq[1]);if(0>(_F3+_Fs|0)){_Fl=_Fp;return null;}else{if((_F3+_Fs|0)>44){_Fl=_Fp;return null;}else{var _Ft=E(_EN),_Fu=E(_Fr[1]);if(0>(_Ft+_Fu|0)){_Fl=_Fp;return null;}else{if((_Ft+_Fu|0)>34){_Fl=_Fp;return null;}else{var _Fv=new T(function(){return B(_Fk(_Fp));}),_Fw=_F3+_Fs|0,_Fx=_Ft+_Fu|0,_Fy=new T(function(){return B(_rI(_Fw,_Fx,_EP));});return [1,[0,[0,_Fw,_Fx],_Fy],_Fv];}}}}}else{_Fl=_Fp;return null;}}}}})(_Fl);if(_Fm!=null){return _Fm;}}};return new F(function(){return _Fk(_F0);});}else{var _Fz=E(_EN),_FA=E(_F2[1]);if(0>(_Fz+_FA|0)){var _FB=function(_FC){while(1){var _FD=(function(_FE){var _FF=E(_FE);if(!_FF[0]){return [0];}else{var _FG=_FF[2],_FH=E(_FF[1]);if(!_FH[0]){_FC=_FG;return null;}else{var _FI=E(_FH[2]);if(!_FI[0]){_FC=_FG;return null;}else{if(!E(_FI[2])[0]){var _FJ=E(_FH[1]);if(0>(_F3+_FJ|0)){_FC=_FG;return null;}else{if((_F3+_FJ|0)>44){_FC=_FG;return null;}else{var _FK=E(_FI[1]);if(0>(_Fz+_FK|0)){_FC=_FG;return null;}else{if((_Fz+_FK|0)>34){_FC=_FG;return null;}else{var _FL=new T(function(){return B(_FB(_FG));}),_FM=_F3+_FJ|0,_FN=_Fz+_FK|0,_FO=new T(function(){return B(_rI(_FM,_FN,_EP));});return [1,[0,[0,_FM,_FN],_FO],_FL];}}}}}else{_FC=_FG;return null;}}}}})(_FC);if(_FD!=null){return _FD;}}};return new F(function(){return _FB(_F0);});}else{if((_Fz+_FA|0)>34){var _FP=function(_FQ){while(1){var _FR=(function(_FS){var _FT=E(_FS);if(!_FT[0]){return [0];}else{var _FU=_FT[2],_FV=E(_FT[1]);if(!_FV[0]){_FQ=_FU;return null;}else{var _FW=E(_FV[2]);if(!_FW[0]){_FQ=_FU;return null;}else{if(!E(_FW[2])[0]){var _FX=E(_FV[1]);if(0>(_F3+_FX|0)){_FQ=_FU;return null;}else{if((_F3+_FX|0)>44){_FQ=_FU;return null;}else{var _FY=E(_FW[1]);if(0>(_Fz+_FY|0)){_FQ=_FU;return null;}else{if((_Fz+_FY|0)>34){_FQ=_FU;return null;}else{var _FZ=new T(function(){return B(_FP(_FU));}),_G0=_F3+_FX|0,_G1=_Fz+_FY|0,_G2=new T(function(){return B(_rI(_G0,_G1,_EP));});return [1,[0,[0,_G0,_G1],_G2],_FZ];}}}}}else{_FQ=_FU;return null;}}}}})(_FQ);if(_FR!=null){return _FR;}}};return new F(function(){return _FP(_F0);});}else{var _G3=new T(function(){var _G4=function(_G5){while(1){var _G6=(function(_G7){var _G8=E(_G7);if(!_G8[0]){return [0];}else{var _G9=_G8[2],_Ga=E(_G8[1]);if(!_Ga[0]){_G5=_G9;return null;}else{var _Gb=E(_Ga[2]);if(!_Gb[0]){_G5=_G9;return null;}else{if(!E(_Gb[2])[0]){var _Gc=E(_Ga[1]);if(0>(_F3+_Gc|0)){_G5=_G9;return null;}else{if((_F3+_Gc|0)>44){_G5=_G9;return null;}else{var _Gd=E(_Gb[1]);if(0>(_Fz+_Gd|0)){_G5=_G9;return null;}else{if((_Fz+_Gd|0)>34){_G5=_G9;return null;}else{var _Ge=new T(function(){return B(_G4(_G9));}),_Gf=_F3+_Gc|0,_Gg=_Fz+_Gd|0,_Gh=new T(function(){return B(_rI(_Gf,_Gg,_EP));});return [1,[0,[0,_Gf,_Gg],_Gh],_Ge];}}}}}else{_G5=_G9;return null;}}}}})(_G5);if(_G6!=null){return _G6;}}};return B(_G4(_F0));}),_Gi=_F3+_F4|0,_Gj=_Fz+_FA|0,_Gk=new T(function(){return B(_rI(_Gi,_Gj,_EP));});return [1,[0,[0,_Gi,_Gj],_Gk],_G3];}}}}}else{_EW=_F0;return null;}}}}})(_EW);if(_EX!=null){return _EX;}}};return B(_Aq(_rF,B(_EV(_B6)),_EQ));}),_Gl=new T(function(){var _Gm=E(_EN);if(0>=_Gm){var _Gn=E(_EM);if(0>=_Gn){return E(_yT);}else{return B(_yW(_Gn));}}else{var _Go=new T(function(){var _Gp=new T(function(){var _Gq=E(_EM);if(0>=_Gq){return E(_yT);}else{return B(_yW(_Gq));}},1);return B(_v(_zi,_Gp));}),_Gr=function(_Gs){var _Gt=E(_Gs);if(_Gt==1){return E(_Go);}else{var _Gu=new T(function(){return B(_Gr(_Gt-1|0));},1);return new F(function(){return _v(_zi,_Gu);});}};return B(_Gr(_Gm));}}),_Gv=B(A(_k8,[_4b,_tH,_ET[1],_k7,_Gl,[0,_EL,[0,_EM,_EN],_EO,_EP,_EU,_ER,_ES],_])),_Gw=_Gv,_Gx=E(_z0),_Gy=jsFind(_Gx);if(!_Gy[0]){return new F(function(){return _Bl(_Gx);});}else{var _Gz=new T(function(){return E(E(_Gw)[2]);}),_GA=new T(function(){var _GB=new T(function(){return E(E(_Gz)[5]);});return B(_zR(_GB));}),_GC=B(A(_k8,[_4b,_tH,_Gy[1],_k7,_GA,_Gz,_])),_GD=E(E(_GC)[2]);if(E(_GD[6])==5){var _GE=E(_3z),_GF=E(_zc)(_GE),_GG=E(_zb),_GH=toJSStr(E(_Bb)),_GI=jsQuerySelectorAll(_GG,_GH);if(!_GI[0]){return E(_Bj);}else{if(!E(_GI[2])[0]){var _GJ=E(_ze),_GK=_GJ(E(_GI[1])),_GL=B(A(_jv,[_4b,_tH,_GK,_Bg,_Bf,[0,_GD[1],_GD[2],_GD[3],_GD[4],_GD[5],_za,_GD[7]],_])),_GM=_GL,_GN=E(_z1),_GO=jsFind(_GN);if(!_GO[0]){return new F(function(){return _Bl(_GN);});}else{var _GP=_GO[1],_GQ=E(_Bp),_GR=new T(function(){return E(E(_GM)[2]);}),_GS=function(_){var _GT=rMV(_GQ);if(!B(_zf(B(_zD(_Bd,E(E(_GT)[7])[2]))))){return _eF;}else{var _GU=E(_zd)(_GE),_GV=jsQuerySelectorAll(_GG,_GH);if(!_GV[0]){return new F(function(){return _yH(_);});}else{if(!E(_GV[2])[0]){var _GW=_GJ(E(_GV[1])),_GX=B(A(_jv,[_4b,_4Q,_GW,_Bg,_Ba,_])),_GY=E(_GP),_GZ=jsQuerySelectorAll(_GY,toJSStr(E(_kF))),_H0=B(_z2(_GZ,_)),_H1=jsQuerySelectorAll(_GY,toJSStr(E(_kE)));return new F(function(){return _z6(_H1,_);});}else{return new F(function(){return _yH(_);});}}}};return new F(function(){return _xO(_GP,_GQ,_GS,_GR,_);});}}else{return E(_Bj);}}}else{return [0,_eF,_GD];}}}};if(!B(_eY(_Bq,39))){return new F(function(){return _EK(_,_EC,_ED,_EE,_EF,_EG,_EH,_EI,_EJ);});}else{var _H2=_ED+1|0;switch(E(B(_yI(_H2,_EE,_EG)))){case 35:var _H3=new T(function(){return E(_EI)+1|0;});return new F(function(){return _EK(_,_EC,_H2,_EE,_EF,_EG,_EH,_H3,_EJ);});break;case 45:var _H4=new T(function(){return E(_EI)+1|0;});return new F(function(){return _EK(_,_EC,_H2,_EE,_EF,_EG,_EH,_H4,_EJ);});break;default:return new F(function(){return _EK(_,_EC,_ED,_EE,_EF,_EG,_EH,_EI,_EJ);});}}};if(!B(_eY(_Bq,37))){return new F(function(){return _EB(_,_Et,_Eu,_Ev,_Ew,_Ex,_Ey,_Ez,_EA);});}else{var _H5=_Eu+(-1)|0;switch(E(B(_yI(_H5,_Ev,_Ex)))){case 35:var _H6=new T(function(){return E(_Ez)+1|0;});return new F(function(){return _EB(_,_Et,_H5,_Ev,_Ew,_Ex,_Ey,_H6,_EA);});break;case 45:var _H7=new T(function(){return E(_Ez)+1|0;});return new F(function(){return _EB(_,_Et,_H5,_Ev,_Ew,_Ex,_Ey,_H7,_EA);});break;default:return new F(function(){return _EB(_,_Et,_Eu,_Ev,_Ew,_Ex,_Ey,_Ez,_EA);});}}};if(!B(_eY(_Bq,40))){var _H8=function(_,_H9,_Ha,_Hb,_Hc,_Hd,_He,_Hf,_Hg){var _Hh=function(_,_Hi,_Hj,_Hk,_Hl,_Hm,_Hn,_Ho,_Hp){var _Hq=jsFind(toJSStr(E(_Bc)));if(!_Hq[0]){return new F(function(){return die(_B9);});}else{var _Hr=new T(function(){var _Hs=function(_Ht){while(1){var _Hu=(function(_Hv){var _Hw=E(_Hv);if(!_Hw[0]){return [0];}else{var _Hx=_Hw[2],_Hy=E(_Hw[1]);if(!_Hy[0]){_Ht=_Hx;return null;}else{var _Hz=E(_Hy[2]);if(!_Hz[0]){_Ht=_Hx;return null;}else{if(!E(_Hz[2])[0]){var _HA=E(_Hy[1]);if(0>(_Hj+_HA|0)){var _HB=function(_HC){while(1){var _HD=(function(_HE){var _HF=E(_HE);if(!_HF[0]){return [0];}else{var _HG=_HF[2],_HH=E(_HF[1]);if(!_HH[0]){_HC=_HG;return null;}else{var _HI=E(_HH[2]);if(!_HI[0]){_HC=_HG;return null;}else{if(!E(_HI[2])[0]){var _HJ=E(_HH[1]);if(0>(_Hj+_HJ|0)){_HC=_HG;return null;}else{if((_Hj+_HJ|0)>44){_HC=_HG;return null;}else{var _HK=E(_Hk),_HL=E(_HI[1]);if(0>(_HK+_HL|0)){_HC=_HG;return null;}else{if((_HK+_HL|0)>34){_HC=_HG;return null;}else{var _HM=new T(function(){return B(_HB(_HG));}),_HN=_Hj+_HJ|0,_HO=_HK+_HL|0,_HP=new T(function(){return B(_rI(_HN,_HO,_Hm));});return [1,[0,[0,_HN,_HO],_HP],_HM];}}}}}else{_HC=_HG;return null;}}}}})(_HC);if(_HD!=null){return _HD;}}};return new F(function(){return _HB(_Hx);});}else{if((_Hj+_HA|0)>44){var _HQ=function(_HR){while(1){var _HS=(function(_HT){var _HU=E(_HT);if(!_HU[0]){return [0];}else{var _HV=_HU[2],_HW=E(_HU[1]);if(!_HW[0]){_HR=_HV;return null;}else{var _HX=E(_HW[2]);if(!_HX[0]){_HR=_HV;return null;}else{if(!E(_HX[2])[0]){var _HY=E(_HW[1]);if(0>(_Hj+_HY|0)){_HR=_HV;return null;}else{if((_Hj+_HY|0)>44){_HR=_HV;return null;}else{var _HZ=E(_Hk),_I0=E(_HX[1]);if(0>(_HZ+_I0|0)){_HR=_HV;return null;}else{if((_HZ+_I0|0)>34){_HR=_HV;return null;}else{var _I1=new T(function(){return B(_HQ(_HV));}),_I2=_Hj+_HY|0,_I3=_HZ+_I0|0,_I4=new T(function(){return B(_rI(_I2,_I3,_Hm));});return [1,[0,[0,_I2,_I3],_I4],_I1];}}}}}else{_HR=_HV;return null;}}}}})(_HR);if(_HS!=null){return _HS;}}};return new F(function(){return _HQ(_Hx);});}else{var _I5=E(_Hk),_I6=E(_Hz[1]);if(0>(_I5+_I6|0)){var _I7=function(_I8){while(1){var _I9=(function(_Ia){var _Ib=E(_Ia);if(!_Ib[0]){return [0];}else{var _Ic=_Ib[2],_Id=E(_Ib[1]);if(!_Id[0]){_I8=_Ic;return null;}else{var _Ie=E(_Id[2]);if(!_Ie[0]){_I8=_Ic;return null;}else{if(!E(_Ie[2])[0]){var _If=E(_Id[1]);if(0>(_Hj+_If|0)){_I8=_Ic;return null;}else{if((_Hj+_If|0)>44){_I8=_Ic;return null;}else{var _Ig=E(_Ie[1]);if(0>(_I5+_Ig|0)){_I8=_Ic;return null;}else{if((_I5+_Ig|0)>34){_I8=_Ic;return null;}else{var _Ih=new T(function(){return B(_I7(_Ic));}),_Ii=_Hj+_If|0,_Ij=_I5+_Ig|0,_Ik=new T(function(){return B(_rI(_Ii,_Ij,_Hm));});return [1,[0,[0,_Ii,_Ij],_Ik],_Ih];}}}}}else{_I8=_Ic;return null;}}}}})(_I8);if(_I9!=null){return _I9;}}};return new F(function(){return _I7(_Hx);});}else{if((_I5+_I6|0)>34){var _Il=function(_Im){while(1){var _In=(function(_Io){var _Ip=E(_Io);if(!_Ip[0]){return [0];}else{var _Iq=_Ip[2],_Ir=E(_Ip[1]);if(!_Ir[0]){_Im=_Iq;return null;}else{var _Is=E(_Ir[2]);if(!_Is[0]){_Im=_Iq;return null;}else{if(!E(_Is[2])[0]){var _It=E(_Ir[1]);if(0>(_Hj+_It|0)){_Im=_Iq;return null;}else{if((_Hj+_It|0)>44){_Im=_Iq;return null;}else{var _Iu=E(_Is[1]);if(0>(_I5+_Iu|0)){_Im=_Iq;return null;}else{if((_I5+_Iu|0)>34){_Im=_Iq;return null;}else{var _Iv=new T(function(){return B(_Il(_Iq));}),_Iw=_Hj+_It|0,_Ix=_I5+_Iu|0,_Iy=new T(function(){return B(_rI(_Iw,_Ix,_Hm));});return [1,[0,[0,_Iw,_Ix],_Iy],_Iv];}}}}}else{_Im=_Iq;return null;}}}}})(_Im);if(_In!=null){return _In;}}};return new F(function(){return _Il(_Hx);});}else{var _Iz=new T(function(){var _IA=function(_IB){while(1){var _IC=(function(_ID){var _IE=E(_ID);if(!_IE[0]){return [0];}else{var _IF=_IE[2],_IG=E(_IE[1]);if(!_IG[0]){_IB=_IF;return null;}else{var _IH=E(_IG[2]);if(!_IH[0]){_IB=_IF;return null;}else{if(!E(_IH[2])[0]){var _II=E(_IG[1]);if(0>(_Hj+_II|0)){_IB=_IF;return null;}else{if((_Hj+_II|0)>44){_IB=_IF;return null;}else{var _IJ=E(_IH[1]);if(0>(_I5+_IJ|0)){_IB=_IF;return null;}else{if((_I5+_IJ|0)>34){_IB=_IF;return null;}else{var _IK=new T(function(){return B(_IA(_IF));}),_IL=_Hj+_II|0,_IM=_I5+_IJ|0,_IN=new T(function(){return B(_rI(_IL,_IM,_Hm));});return [1,[0,[0,_IL,_IM],_IN],_IK];}}}}}else{_IB=_IF;return null;}}}}})(_IB);if(_IC!=null){return _IC;}}};return B(_IA(_Hx));}),_IO=_Hj+_HA|0,_IP=_I5+_I6|0,_IQ=new T(function(){return B(_rI(_IO,_IP,_Hm));});return [1,[0,[0,_IO,_IP],_IQ],_Iz];}}}}}else{_Ht=_Hx;return null;}}}}})(_Ht);if(_Hu!=null){return _Hu;}}};return B(_Aq(_rF,B(_Hs(_B6)),_Hn));}),_IR=new T(function(){var _IS=E(_Hk);if(0>=_IS){if(0>=_Hj){return E(_yT);}else{return B(_yW(_Hj));}}else{var _IT=new T(function(){var _IU=new T(function(){if(0>=_Hj){return E(_yT);}else{return B(_yW(_Hj));}},1);return B(_v(_zi,_IU));}),_IV=function(_IW){var _IX=E(_IW);if(_IX==1){return E(_IT);}else{var _IY=new T(function(){return B(_IV(_IX-1|0));},1);return new F(function(){return _v(_zi,_IY);});}};return B(_IV(_IS));}}),_IZ=B(A(_k8,[_4b,_tH,_Hq[1],_k7,_IR,[0,_Hi,[0,_Hj,_Hk],_Hl,_Hm,_Hr,_Ho,_Hp],_])),_J0=_IZ,_J1=E(_z0),_J2=jsFind(_J1);if(!_J2[0]){return new F(function(){return _Bl(_J1);});}else{var _J3=new T(function(){return E(E(_J0)[2]);}),_J4=new T(function(){var _J5=new T(function(){return E(E(_J3)[5]);});return B(_zR(_J5));}),_J6=B(A(_k8,[_4b,_tH,_J2[1],_k7,_J4,_J3,_])),_J7=E(E(_J6)[2]);if(E(_J7[6])==5){var _J8=E(_3z),_J9=E(_zc)(_J8),_Ja=E(_zb),_Jb=toJSStr(E(_Bb)),_Jc=jsQuerySelectorAll(_Ja,_Jb);if(!_Jc[0]){return E(_Bj);}else{if(!E(_Jc[2])[0]){var _Jd=E(_ze),_Je=_Jd(E(_Jc[1])),_Jf=B(A(_jv,[_4b,_tH,_Je,_Bg,_Bf,[0,_J7[1],_J7[2],_J7[3],_J7[4],_J7[5],_za,_J7[7]],_])),_Jg=_Jf,_Jh=E(_z1),_Ji=jsFind(_Jh);if(!_Ji[0]){return new F(function(){return _Bl(_Jh);});}else{var _Jj=_Ji[1],_Jk=E(_Bp),_Jl=new T(function(){return E(E(_Jg)[2]);}),_Jm=function(_){var _Jn=rMV(_Jk);if(!B(_zf(B(_zD(_Bd,E(E(_Jn)[7])[2]))))){return _eF;}else{var _Jo=E(_zd)(_J8),_Jp=jsQuerySelectorAll(_Ja,_Jb);if(!_Jp[0]){return new F(function(){return _yH(_);});}else{if(!E(_Jp[2])[0]){var _Jq=_Jd(E(_Jp[1])),_Jr=B(A(_jv,[_4b,_4Q,_Jq,_Bg,_Ba,_])),_Js=E(_Jj),_Jt=jsQuerySelectorAll(_Js,toJSStr(E(_kF))),_Ju=B(_z2(_Jt,_)),_Jv=jsQuerySelectorAll(_Js,toJSStr(E(_kE)));return new F(function(){return _z6(_Jv,_);});}else{return new F(function(){return _yH(_);});}}}};return new F(function(){return _xO(_Jj,_Jk,_Jm,_Jl,_);});}}else{return E(_Bj);}}}else{return [0,_eF,_J7];}}}};if(!B(_eY(_Bq,39))){return new F(function(){return _Hh(_,_H9,_Ha,_Hb,_Hc,_Hd,_He,_Hf,_Hg);});}else{var _Jw=_Ha+1|0;switch(E(B(_yI(_Jw,_Hb,_Hd)))){case 35:var _Jx=new T(function(){return E(_Hf)+1|0;});return new F(function(){return _Hh(_,_H9,_Jw,_Hb,_Hc,_Hd,_He,_Jx,_Hg);});break;case 45:var _Jy=new T(function(){return E(_Hf)+1|0;});return new F(function(){return _Hh(_,_H9,_Jw,_Hb,_Hc,_Hd,_He,_Jy,_Hg);});break;default:return new F(function(){return _Hh(_,_H9,_Ha,_Hb,_Hc,_Hd,_He,_Hf,_Hg);});}}};if(!B(_eY(_Bq,37))){var _Jz=function(_,_JA,_JB,_JC,_JD,_JE,_JF,_JG,_JH){var _JI=jsFind(toJSStr(E(_Bc)));if(!_JI[0]){return new F(function(){return die(_B9);});}else{var _JJ=new T(function(){var _JK=function(_JL){while(1){var _JM=(function(_JN){var _JO=E(_JN);if(!_JO[0]){return [0];}else{var _JP=_JO[2],_JQ=E(_JO[1]);if(!_JQ[0]){_JL=_JP;return null;}else{var _JR=E(_JQ[2]);if(!_JR[0]){_JL=_JP;return null;}else{if(!E(_JR[2])[0]){var _JS=E(_JQ[1]);if(0>(_JB+_JS|0)){var _JT=function(_JU){while(1){var _JV=(function(_JW){var _JX=E(_JW);if(!_JX[0]){return [0];}else{var _JY=_JX[2],_JZ=E(_JX[1]);if(!_JZ[0]){_JU=_JY;return null;}else{var _K0=E(_JZ[2]);if(!_K0[0]){_JU=_JY;return null;}else{if(!E(_K0[2])[0]){var _K1=E(_JZ[1]);if(0>(_JB+_K1|0)){_JU=_JY;return null;}else{if((_JB+_K1|0)>44){_JU=_JY;return null;}else{var _K2=E(_JC),_K3=E(_K0[1]);if(0>(_K2+_K3|0)){_JU=_JY;return null;}else{if((_K2+_K3|0)>34){_JU=_JY;return null;}else{var _K4=new T(function(){return B(_JT(_JY));}),_K5=_JB+_K1|0,_K6=_K2+_K3|0,_K7=new T(function(){return B(_rI(_K5,_K6,_JE));});return [1,[0,[0,_K5,_K6],_K7],_K4];}}}}}else{_JU=_JY;return null;}}}}})(_JU);if(_JV!=null){return _JV;}}};return new F(function(){return _JT(_JP);});}else{if((_JB+_JS|0)>44){var _K8=function(_K9){while(1){var _Ka=(function(_Kb){var _Kc=E(_Kb);if(!_Kc[0]){return [0];}else{var _Kd=_Kc[2],_Ke=E(_Kc[1]);if(!_Ke[0]){_K9=_Kd;return null;}else{var _Kf=E(_Ke[2]);if(!_Kf[0]){_K9=_Kd;return null;}else{if(!E(_Kf[2])[0]){var _Kg=E(_Ke[1]);if(0>(_JB+_Kg|0)){_K9=_Kd;return null;}else{if((_JB+_Kg|0)>44){_K9=_Kd;return null;}else{var _Kh=E(_JC),_Ki=E(_Kf[1]);if(0>(_Kh+_Ki|0)){_K9=_Kd;return null;}else{if((_Kh+_Ki|0)>34){_K9=_Kd;return null;}else{var _Kj=new T(function(){return B(_K8(_Kd));}),_Kk=_JB+_Kg|0,_Kl=_Kh+_Ki|0,_Km=new T(function(){return B(_rI(_Kk,_Kl,_JE));});return [1,[0,[0,_Kk,_Kl],_Km],_Kj];}}}}}else{_K9=_Kd;return null;}}}}})(_K9);if(_Ka!=null){return _Ka;}}};return new F(function(){return _K8(_JP);});}else{var _Kn=E(_JC),_Ko=E(_JR[1]);if(0>(_Kn+_Ko|0)){var _Kp=function(_Kq){while(1){var _Kr=(function(_Ks){var _Kt=E(_Ks);if(!_Kt[0]){return [0];}else{var _Ku=_Kt[2],_Kv=E(_Kt[1]);if(!_Kv[0]){_Kq=_Ku;return null;}else{var _Kw=E(_Kv[2]);if(!_Kw[0]){_Kq=_Ku;return null;}else{if(!E(_Kw[2])[0]){var _Kx=E(_Kv[1]);if(0>(_JB+_Kx|0)){_Kq=_Ku;return null;}else{if((_JB+_Kx|0)>44){_Kq=_Ku;return null;}else{var _Ky=E(_Kw[1]);if(0>(_Kn+_Ky|0)){_Kq=_Ku;return null;}else{if((_Kn+_Ky|0)>34){_Kq=_Ku;return null;}else{var _Kz=new T(function(){return B(_Kp(_Ku));}),_KA=_JB+_Kx|0,_KB=_Kn+_Ky|0,_KC=new T(function(){return B(_rI(_KA,_KB,_JE));});return [1,[0,[0,_KA,_KB],_KC],_Kz];}}}}}else{_Kq=_Ku;return null;}}}}})(_Kq);if(_Kr!=null){return _Kr;}}};return new F(function(){return _Kp(_JP);});}else{if((_Kn+_Ko|0)>34){var _KD=function(_KE){while(1){var _KF=(function(_KG){var _KH=E(_KG);if(!_KH[0]){return [0];}else{var _KI=_KH[2],_KJ=E(_KH[1]);if(!_KJ[0]){_KE=_KI;return null;}else{var _KK=E(_KJ[2]);if(!_KK[0]){_KE=_KI;return null;}else{if(!E(_KK[2])[0]){var _KL=E(_KJ[1]);if(0>(_JB+_KL|0)){_KE=_KI;return null;}else{if((_JB+_KL|0)>44){_KE=_KI;return null;}else{var _KM=E(_KK[1]);if(0>(_Kn+_KM|0)){_KE=_KI;return null;}else{if((_Kn+_KM|0)>34){_KE=_KI;return null;}else{var _KN=new T(function(){return B(_KD(_KI));}),_KO=_JB+_KL|0,_KP=_Kn+_KM|0,_KQ=new T(function(){return B(_rI(_KO,_KP,_JE));});return [1,[0,[0,_KO,_KP],_KQ],_KN];}}}}}else{_KE=_KI;return null;}}}}})(_KE);if(_KF!=null){return _KF;}}};return new F(function(){return _KD(_JP);});}else{var _KR=new T(function(){var _KS=function(_KT){while(1){var _KU=(function(_KV){var _KW=E(_KV);if(!_KW[0]){return [0];}else{var _KX=_KW[2],_KY=E(_KW[1]);if(!_KY[0]){_KT=_KX;return null;}else{var _KZ=E(_KY[2]);if(!_KZ[0]){_KT=_KX;return null;}else{if(!E(_KZ[2])[0]){var _L0=E(_KY[1]);if(0>(_JB+_L0|0)){_KT=_KX;return null;}else{if((_JB+_L0|0)>44){_KT=_KX;return null;}else{var _L1=E(_KZ[1]);if(0>(_Kn+_L1|0)){_KT=_KX;return null;}else{if((_Kn+_L1|0)>34){_KT=_KX;return null;}else{var _L2=new T(function(){return B(_KS(_KX));}),_L3=_JB+_L0|0,_L4=_Kn+_L1|0,_L5=new T(function(){return B(_rI(_L3,_L4,_JE));});return [1,[0,[0,_L3,_L4],_L5],_L2];}}}}}else{_KT=_KX;return null;}}}}})(_KT);if(_KU!=null){return _KU;}}};return B(_KS(_JP));}),_L6=_JB+_JS|0,_L7=_Kn+_Ko|0,_L8=new T(function(){return B(_rI(_L6,_L7,_JE));});return [1,[0,[0,_L6,_L7],_L8],_KR];}}}}}else{_JL=_JP;return null;}}}}})(_JL);if(_JM!=null){return _JM;}}};return B(_Aq(_rF,B(_JK(_B6)),_JF));}),_L9=new T(function(){var _La=E(_JC);if(0>=_La){if(0>=_JB){return E(_yT);}else{return B(_yW(_JB));}}else{var _Lb=new T(function(){var _Lc=new T(function(){if(0>=_JB){return E(_yT);}else{return B(_yW(_JB));}},1);return B(_v(_zi,_Lc));}),_Ld=function(_Le){var _Lf=E(_Le);if(_Lf==1){return E(_Lb);}else{var _Lg=new T(function(){return B(_Ld(_Lf-1|0));},1);return new F(function(){return _v(_zi,_Lg);});}};return B(_Ld(_La));}}),_Lh=B(A(_k8,[_4b,_tH,_JI[1],_k7,_L9,[0,_JA,[0,_JB,_JC],_JD,_JE,_JJ,_JG,_JH],_])),_Li=_Lh,_Lj=E(_z0),_Lk=jsFind(_Lj);if(!_Lk[0]){return new F(function(){return _Bl(_Lj);});}else{var _Ll=new T(function(){return E(E(_Li)[2]);}),_Lm=new T(function(){var _Ln=new T(function(){return E(E(_Ll)[5]);});return B(_zR(_Ln));}),_Lo=B(A(_k8,[_4b,_tH,_Lk[1],_k7,_Lm,_Ll,_])),_Lp=E(E(_Lo)[2]);if(E(_Lp[6])==5){var _Lq=E(_3z),_Lr=E(_zc)(_Lq),_Ls=E(_zb),_Lt=toJSStr(E(_Bb)),_Lu=jsQuerySelectorAll(_Ls,_Lt);if(!_Lu[0]){return E(_Bj);}else{if(!E(_Lu[2])[0]){var _Lv=E(_ze),_Lw=_Lv(E(_Lu[1])),_Lx=B(A(_jv,[_4b,_tH,_Lw,_Bg,_Bf,[0,_Lp[1],_Lp[2],_Lp[3],_Lp[4],_Lp[5],_za,_Lp[7]],_])),_Ly=_Lx,_Lz=E(_z1),_LA=jsFind(_Lz);if(!_LA[0]){return new F(function(){return _Bl(_Lz);});}else{var _LB=_LA[1],_LC=E(_Bp),_LD=new T(function(){return E(E(_Ly)[2]);}),_LE=function(_){var _LF=rMV(_LC);if(!B(_zf(B(_zD(_Bd,E(E(_LF)[7])[2]))))){return _eF;}else{var _LG=E(_zd)(_Lq),_LH=jsQuerySelectorAll(_Ls,_Lt);if(!_LH[0]){return new F(function(){return _yH(_);});}else{if(!E(_LH[2])[0]){var _LI=_Lv(E(_LH[1])),_LJ=B(A(_jv,[_4b,_4Q,_LI,_Bg,_Ba,_])),_LK=E(_LB),_LL=jsQuerySelectorAll(_LK,toJSStr(E(_kF))),_LM=B(_z2(_LL,_)),_LN=jsQuerySelectorAll(_LK,toJSStr(E(_kE)));return new F(function(){return _z6(_LN,_);});}else{return new F(function(){return _yH(_);});}}}};return new F(function(){return _xO(_LB,_LC,_LE,_LD,_);});}}else{return E(_Bj);}}}else{return [0,_eF,_Lp];}}}};if(!B(_eY(_Bq,39))){var _LO=jsFind(toJSStr(E(_Bc)));if(!_LO[0]){return new F(function(){return die(_B9);});}else{var _LP=new T(function(){var _LQ=function(_LR){while(1){var _LS=(function(_LT){var _LU=E(_LT);if(!_LU[0]){return [0];}else{var _LV=_LU[2],_LW=E(_LU[1]);if(!_LW[0]){_LR=_LV;return null;}else{var _LX=E(_LW[2]);if(!_LX[0]){_LR=_LV;return null;}else{if(!E(_LX[2])[0]){var _LY=E(_Bx),_LZ=E(_LW[1]);if(0>(_LY+_LZ|0)){var _M0=function(_M1){while(1){var _M2=(function(_M3){var _M4=E(_M3);if(!_M4[0]){return [0];}else{var _M5=_M4[2],_M6=E(_M4[1]);if(!_M6[0]){_M1=_M5;return null;}else{var _M7=E(_M6[2]);if(!_M7[0]){_M1=_M5;return null;}else{if(!E(_M7[2])[0]){var _M8=E(_M6[1]);if(0>(_LY+_M8|0)){_M1=_M5;return null;}else{if((_LY+_M8|0)>44){_M1=_M5;return null;}else{var _M9=E(_By),_Ma=E(_M7[1]);if(0>(_M9+_Ma|0)){_M1=_M5;return null;}else{if((_M9+_Ma|0)>34){_M1=_M5;return null;}else{var _Mb=new T(function(){return B(_M0(_M5));}),_Mc=_LY+_M8|0,_Md=_M9+_Ma|0,_Me=new T(function(){return B(_rI(_Mc,_Md,_Bs));});return [1,[0,[0,_Mc,_Md],_Me],_Mb];}}}}}else{_M1=_M5;return null;}}}}})(_M1);if(_M2!=null){return _M2;}}};return new F(function(){return _M0(_LV);});}else{if((_LY+_LZ|0)>44){var _Mf=function(_Mg){while(1){var _Mh=(function(_Mi){var _Mj=E(_Mi);if(!_Mj[0]){return [0];}else{var _Mk=_Mj[2],_Ml=E(_Mj[1]);if(!_Ml[0]){_Mg=_Mk;return null;}else{var _Mm=E(_Ml[2]);if(!_Mm[0]){_Mg=_Mk;return null;}else{if(!E(_Mm[2])[0]){var _Mn=E(_Ml[1]);if(0>(_LY+_Mn|0)){_Mg=_Mk;return null;}else{if((_LY+_Mn|0)>44){_Mg=_Mk;return null;}else{var _Mo=E(_By),_Mp=E(_Mm[1]);if(0>(_Mo+_Mp|0)){_Mg=_Mk;return null;}else{if((_Mo+_Mp|0)>34){_Mg=_Mk;return null;}else{var _Mq=new T(function(){return B(_Mf(_Mk));}),_Mr=_LY+_Mn|0,_Ms=_Mo+_Mp|0,_Mt=new T(function(){return B(_rI(_Mr,_Ms,_Bs));});return [1,[0,[0,_Mr,_Ms],_Mt],_Mq];}}}}}else{_Mg=_Mk;return null;}}}}})(_Mg);if(_Mh!=null){return _Mh;}}};return new F(function(){return _Mf(_LV);});}else{var _Mu=E(_By),_Mv=E(_LX[1]);if(0>(_Mu+_Mv|0)){var _Mw=function(_Mx){while(1){var _My=(function(_Mz){var _MA=E(_Mz);if(!_MA[0]){return [0];}else{var _MB=_MA[2],_MC=E(_MA[1]);if(!_MC[0]){_Mx=_MB;return null;}else{var _MD=E(_MC[2]);if(!_MD[0]){_Mx=_MB;return null;}else{if(!E(_MD[2])[0]){var _ME=E(_MC[1]);if(0>(_LY+_ME|0)){_Mx=_MB;return null;}else{if((_LY+_ME|0)>44){_Mx=_MB;return null;}else{var _MF=E(_MD[1]);if(0>(_Mu+_MF|0)){_Mx=_MB;return null;}else{if((_Mu+_MF|0)>34){_Mx=_MB;return null;}else{var _MG=new T(function(){return B(_Mw(_MB));}),_MH=_LY+_ME|0,_MI=_Mu+_MF|0,_MJ=new T(function(){return B(_rI(_MH,_MI,_Bs));});return [1,[0,[0,_MH,_MI],_MJ],_MG];}}}}}else{_Mx=_MB;return null;}}}}})(_Mx);if(_My!=null){return _My;}}};return new F(function(){return _Mw(_LV);});}else{if((_Mu+_Mv|0)>34){var _MK=function(_ML){while(1){var _MM=(function(_MN){var _MO=E(_MN);if(!_MO[0]){return [0];}else{var _MP=_MO[2],_MQ=E(_MO[1]);if(!_MQ[0]){_ML=_MP;return null;}else{var _MR=E(_MQ[2]);if(!_MR[0]){_ML=_MP;return null;}else{if(!E(_MR[2])[0]){var _MS=E(_MQ[1]);if(0>(_LY+_MS|0)){_ML=_MP;return null;}else{if((_LY+_MS|0)>44){_ML=_MP;return null;}else{var _MT=E(_MR[1]);if(0>(_Mu+_MT|0)){_ML=_MP;return null;}else{if((_Mu+_MT|0)>34){_ML=_MP;return null;}else{var _MU=new T(function(){return B(_MK(_MP));}),_MV=_LY+_MS|0,_MW=_Mu+_MT|0,_MX=new T(function(){return B(_rI(_MV,_MW,_Bs));});return [1,[0,[0,_MV,_MW],_MX],_MU];}}}}}else{_ML=_MP;return null;}}}}})(_ML);if(_MM!=null){return _MM;}}};return new F(function(){return _MK(_LV);});}else{var _MY=new T(function(){var _MZ=function(_N0){while(1){var _N1=(function(_N2){var _N3=E(_N2);if(!_N3[0]){return [0];}else{var _N4=_N3[2],_N5=E(_N3[1]);if(!_N5[0]){_N0=_N4;return null;}else{var _N6=E(_N5[2]);if(!_N6[0]){_N0=_N4;return null;}else{if(!E(_N6[2])[0]){var _N7=E(_N5[1]);if(0>(_LY+_N7|0)){_N0=_N4;return null;}else{if((_LY+_N7|0)>44){_N0=_N4;return null;}else{var _N8=E(_N6[1]);if(0>(_Mu+_N8|0)){_N0=_N4;return null;}else{if((_Mu+_N8|0)>34){_N0=_N4;return null;}else{var _N9=new T(function(){return B(_MZ(_N4));}),_Na=_LY+_N7|0,_Nb=_Mu+_N8|0,_Nc=new T(function(){return B(_rI(_Na,_Nb,_Bs));});return [1,[0,[0,_Na,_Nb],_Nc],_N9];}}}}}else{_N0=_N4;return null;}}}}})(_N0);if(_N1!=null){return _N1;}}};return B(_MZ(_LV));}),_Nd=_LY+_LZ|0,_Ne=_Mu+_Mv|0,_Nf=new T(function(){return B(_rI(_Nd,_Ne,_Bs));});return [1,[0,[0,_Nd,_Ne],_Nf],_MY];}}}}}else{_LR=_LV;return null;}}}}})(_LR);if(_LS!=null){return _LS;}}};return B(_Aq(_rF,B(_LQ(_B6)),_Bt));}),_Ng=new T(function(){var _Nh=E(_By);if(0>=_Nh){var _Ni=E(_Bx);if(0>=_Ni){return E(_yT);}else{return B(_yW(_Ni));}}else{var _Nj=new T(function(){var _Nk=new T(function(){var _Nl=E(_Bx);if(0>=_Nl){return E(_yT);}else{return B(_yW(_Nl));}},1);return B(_v(_zi,_Nk));}),_Nm=function(_Nn){var _No=E(_Nn);if(_No==1){return E(_Nj);}else{var _Np=new T(function(){return B(_Nm(_No-1|0));},1);return new F(function(){return _v(_zi,_Np);});}};return B(_Nm(_Nh));}}),_Nq=B(A(_k8,[_4b,_tH,_LO[1],_k7,_Ng,[0,_Bq,[0,_Bx,_By],_Bw,_Bs,_LP,_Bu,_Bv],_])),_Nr=_Nq,_Ns=E(_z0),_Nt=jsFind(_Ns);if(!_Nt[0]){return new F(function(){return _Bl(_Ns);});}else{var _Nu=new T(function(){return E(E(_Nr)[2]);}),_Nv=new T(function(){var _Nw=new T(function(){return E(E(_Nu)[5]);});return B(_zR(_Nw));}),_Nx=B(A(_k8,[_4b,_tH,_Nt[1],_k7,_Nv,_Nu,_])),_Ny=E(E(_Nx)[2]);if(E(_Ny[6])==5){var _Nz=E(_3z),_NA=E(_zc)(_Nz),_NB=E(_zb),_NC=toJSStr(E(_Bb)),_ND=jsQuerySelectorAll(_NB,_NC);if(!_ND[0]){return E(_Bj);}else{if(!E(_ND[2])[0]){var _NE=E(_ze),_NF=_NE(E(_ND[1])),_NG=B(A(_jv,[_4b,_tH,_NF,_Bg,_Bf,[0,_Ny[1],_Ny[2],_Ny[3],_Ny[4],_Ny[5],_za,_Ny[7]],_])),_NH=_NG,_NI=E(_z1),_NJ=jsFind(_NI);if(!_NJ[0]){return new F(function(){return _Bl(_NI);});}else{var _NK=_NJ[1],_NL=E(_Bp),_NM=new T(function(){return E(E(_NH)[2]);}),_NN=function(_){var _NO=rMV(_NL);if(!B(_zf(B(_zD(_Bd,E(E(_NO)[7])[2]))))){return _eF;}else{var _NP=E(_zd)(_Nz),_NQ=jsQuerySelectorAll(_NB,_NC);if(!_NQ[0]){return new F(function(){return _yH(_);});}else{if(!E(_NQ[2])[0]){var _NR=_NE(E(_NQ[1])),_NS=B(A(_jv,[_4b,_4Q,_NR,_Bg,_Ba,_])),_NT=E(_NK),_NU=jsQuerySelectorAll(_NT,toJSStr(E(_kF))),_NV=B(_z2(_NU,_)),_NW=jsQuerySelectorAll(_NT,toJSStr(E(_kE)));return new F(function(){return _z6(_NW,_);});}else{return new F(function(){return _yH(_);});}}}};return new F(function(){return _xO(_NK,_NL,_NN,_NM,_);});}}else{return E(_Bj);}}}else{return [0,_eF,_Ny];}}}}else{var _NX=E(_Bx),_NY=_NX+1|0;switch(E(B(_yI(_NY,_By,_Bs)))){case 35:var _NZ=new T(function(){return E(_Bu)+1|0;});return new F(function(){return _Jz(_,_Bq,_NY,_By,_Bw,_Bs,_Bt,_NZ,_Bv);});break;case 45:var _O0=new T(function(){return E(_Bu)+1|0;});return new F(function(){return _Jz(_,_Bq,_NY,_By,_Bw,_Bs,_Bt,_O0,_Bv);});break;default:return new F(function(){return _Jz(_,_Bq,_NX,_By,_Bw,_Bs,_Bt,_Bu,_Bv);});}}}else{var _O1=E(_Bx),_O2=_O1+(-1)|0;switch(E(B(_yI(_O2,_By,_Bs)))){case 35:var _O3=new T(function(){return E(_Bu)+1|0;});return new F(function(){return _H8(_,_Bq,_O2,_By,_Bw,_Bs,_Bt,_O3,_Bv);});break;case 45:var _O4=new T(function(){return E(_Bu)+1|0;});return new F(function(){return _H8(_,_Bq,_O2,_By,_Bw,_Bs,_Bt,_O4,_Bv);});break;default:return new F(function(){return _H8(_,_Bq,_O1,_By,_Bw,_Bs,_Bt,_Bu,_Bv);});}}}else{var _O5=E(_Bx),_O6=new T(function(){return E(_By)+1|0;});switch(E(B(_yI(_O5,_O6,_Bs)))){case 35:var _O7=new T(function(){return E(_Bu)+1|0;});return new F(function(){return _Es(_,_Bq,_O5,_O6,_Bw,_Bs,_Bt,_O7,_Bv);});break;case 45:var _O8=new T(function(){return E(_Bu)+1|0;});return new F(function(){return _Es(_,_Bq,_O5,_O6,_Bw,_Bs,_Bt,_O8,_Bv);});break;default:return new F(function(){return _Es(_,_Bq,_O5,_By,_Bw,_Bs,_Bt,_Bu,_Bv);});}}}else{var _O9=E(_Bx),_Oa=new T(function(){return E(_By)+(-1)|0;});switch(E(B(_yI(_O9,_Oa,_Bs)))){case 35:var _Ob=new T(function(){return E(_Bu)+1|0;});return new F(function(){return _Bz(_,_Bq,_O9,_Oa,_Bw,_Bs,_Bt,_Ob,_Bv);});break;case 45:var _Oc=new T(function(){return E(_Bu)+1|0;});return new F(function(){return _Bz(_,_Bq,_O9,_Oa,_Bw,_Bs,_Bt,_Oc,_Bv);});break;default:return new F(function(){return _Bz(_,_Bq,_O9,_By,_Bw,_Bs,_Bt,_Bu,_Bv);});}}},_Od=function(_Oe,_Of){while(1){var _Og=E(_Oe);if(!_Og[0]){return (E(_Of)[0]==0)?true:false;}else{var _Oh=E(_Of);if(!_Oh[0]){return false;}else{if(E(_Og[1])!=E(_Oh[1])){return false;}else{_Oe=_Og[2];_Of=_Oh[2];continue;}}}}},_Oi=function(_Oj,_Ok){return new F(function(){return _Od(E(_Oj)[1],E(_Ok)[1]);});},_Ol=function(_Om,_On){while(1){var _Oo=E(_Om);if(!_Oo[0]){return E(_On);}else{_Om=_Oo[2];var _Op=_On+1|0;_On=_Op;continue;}}},_Oq="party-display",_Or="make-party",_Os=[2],_Ot=new T(function(){return B(_zj(0,2147483647));}),_Ou=function(_Ov,_Ow){var _Ox=E(_Ov);if(!_Ox[0]){return [0];}else{var _Oy=_Ox[2],_Oz=E(_Ow);if(!_Oz[0]){return [0];}else{var _OA=_Oz[2],_OB=new T(function(){return B(_Ou(_Oy,_OA));});return [1,[0,_Ox[1],_Oz[1]],_OB];}}},_OC=new T(function(){return B(_Ou(_Ot,_11));}),_OD=function(_OE,_OF,_OG){var _OH=E(_OG);switch(_OH[0]){case 0:var _OI=_OH[1],_OJ=_OH[2],_OK=_OH[3],_OL=_OH[4],_OM=_OJ>>>0;if(((_OE>>>0&((_OM-1>>>0^4294967295)>>>0^_OM)>>>0)>>>0&4294967295)==_OI){return ((_OE>>>0&_OM)>>>0==0)?[0,_OI,_OJ,E(B(_OD(_OE,_OF,_OK))),E(_OL)]:[0,_OI,_OJ,E(_OK),E(B(_OD(_OE,_OF,_OL)))];}else{var _ON=(_OE>>>0^_OI>>>0)>>>0,_OO=(_ON|_ON>>>1)>>>0,_OP=(_OO|_OO>>>2)>>>0,_OQ=(_OP|_OP>>>4)>>>0,_OR=(_OQ|_OQ>>>8)>>>0,_OS=(_OR|_OR>>>16)>>>0,_OT=(_OS^_OS>>>1)>>>0&4294967295,_OU=_OT>>>0;return ((_OE>>>0&_OU)>>>0==0)?[0,(_OE>>>0&((_OU-1>>>0^4294967295)>>>0^_OU)>>>0)>>>0&4294967295,_OT,[1,_OE,_OF],E(_OH)]:[0,(_OE>>>0&((_OU-1>>>0^4294967295)>>>0^_OU)>>>0)>>>0&4294967295,_OT,E(_OH),[1,_OE,_OF]];}break;case 1:var _OV=_OH[1];if(_OE!=_OV){var _OW=(_OE>>>0^_OV>>>0)>>>0,_OX=(_OW|_OW>>>1)>>>0,_OY=(_OX|_OX>>>2)>>>0,_OZ=(_OY|_OY>>>4)>>>0,_P0=(_OZ|_OZ>>>8)>>>0,_P1=(_P0|_P0>>>16)>>>0,_P2=(_P1^_P1>>>1)>>>0&4294967295,_P3=_P2>>>0;return ((_OE>>>0&_P3)>>>0==0)?[0,(_OE>>>0&((_P3-1>>>0^4294967295)>>>0^_P3)>>>0)>>>0&4294967295,_P2,[1,_OE,_OF],E(_OH)]:[0,(_OE>>>0&((_P3-1>>>0^4294967295)>>>0^_P3)>>>0)>>>0&4294967295,_P2,E(_OH),[1,_OE,_OF]];}else{return [1,_OE,_OF];}break;default:return [1,_OE,_OF];}},_P4=function(_P5,_P6){while(1){var _P7=E(_P6);if(!_P7[0]){return E(_P5);}else{var _P8=E(_P7[1]),_P9=B(_OD(E(_P8[1]),_P8[2],_P5));_P6=_P7[2];_P5=_P9;continue;}}},_Pa=new T(function(){return B(_P4(_Os,_OC));}),_Pb=new T(function(){return B(_Ol(_11,0));}),_Pc=0,_Pd=[0,_Pc,_Pb,_Pa],_Pe=30,_Pf=1,_Pg=80,_Ph=function(_Pi,_Pj,_Pk){var _Pl=E(_Pk);if(!_Pl[0]){return [0];}else{var _Pm=_Pl[1],_Pn=_Pl[2];if(!B(A(_Pi,[_Pj,_Pm]))){var _Po=new T(function(){return B(_Ph(_Pi,_Pj,_Pn));});return [1,_Pm,_Po];}else{return E(_Pn);}}},_Pp=10,_Pq=20,_Pr=40,_Ps=function(_Pt,_Pu){var _Pv=function(_Pw,_Px){while(1){var _Py=(function(_Pz,_PA){var _PB=E(_Pz);if(!_PB[0]){return [0];}else{var _PC=_PB[2];if(!B(A(_Pt,[_PB[1]]))){_Pw=_PC;var _PD=_PA+1|0;_Px=_PD;return null;}else{var _PE=new T(function(){return B(_Pv(_PC,_PA+1|0));});return [1,_PA,_PE];}}})(_Pw,_Px);if(_Py!=null){return _Py;}}},_PF=B(_Pv(_Pu,0));return (_PF[0]==0)?[0]:[1,_PF[1]];},_PG=50,_PH=85,_PI=60,_PJ=new T(function(){return B(unCStr("<button type=\"button\" class=\"btn btn-default btn-sm\" id=\"remove-party-go\">\u30e1\u30f3\u30d0\u30fc\u304b\u3089\u306f\u305a\u3059</button>"));}),_PK=new T(function(){return B(unAppCStr(")</button>&nbsp;",_PJ));}),_PL=new T(function(){return B(unCStr(" #join-party-btn"));}),_PM=new T(function(){return B(unCStr("#remove-party-go"));}),_PN=new T(function(){return B(unCStr("<button type=\"button\" class=\"btn btn-primary btn-sm\" disabled=\"disabled\">\u30d1\u30fc\u30c6\u30a3\u30e1\u30f3\u30d0\u30fc("));}),_PO=new T(function(){return B(unCStr("<button type=\"button\" class=\"btn btn-primary btn-sm\" disabled=\"disabled\">\u30d1\u30fc\u30c6\u30a3\u306b\u5165\u308c\u308b</button>"));}),_PP=new T(function(){return B(unCStr("#join-party-go"));}),_PQ=new T(function(){return B(unCStr("<button type=\"button\" class=\"btn btn-primary btn-sm\" id=\"join-party-go\">\u30d1\u30fc\u30c6\u30a3\u306b\u5165\u308c\u308b</button>"));}),_PR=55,_PS=70,_PT=45,_PU=new T(function(){return B(unCStr("\u30ae\u30e3\u30f3\u30d6\u30e9\u30fc"));}),_PV=[0,_PU,_Pe,_PT,_Pe,_PR,_PI,_PH,_Pf,_PG,_PG,_PS,_PS,_Pd],_PW=35,_PX=65,_PY=new T(function(){return B(unCStr("\u8e0a\u308a\u5b50"));}),_PZ=75,_Q0=[0,_PY,_PX,_Pe,_PW,_PR,_PZ,_Pg,_Pf,_PR,_PR,_PX,_PX,_Pd],_Q1=[1,_Q0,_11],_Q2=[1,_PV,_Q1],_Q3=25,_Q4=90,_Q5=new T(function(){return B(unCStr("\u546a\u8853\u5e2b"));}),_Q6=[0,_Q5,_Pq,_PX,_Q4,_Q3,_Pe,_PX,_Pf,_Pr,_Pr,_Pg,_Pg,_Pd],_Q7=[1,_Q6,_Q2],_Q8=new T(function(){return B(unCStr("\u72c2\u4eba"));}),_Q9=[0,_Q8,_PH,_Pc,_Pc,_Pe,_Pp,_PI,_Pf,_Pg,_Pg,_Pc,_Pc,_Pd],_Qa=[1,_Q9,_Q7],_Qb=new T(function(){return B(unCStr(","));}),_Qc=new T(function(){return B(unCStr("\u30d7\u30ea\u30f3\u30bb\u30b9"));}),_Qd=[0,_Qc,_Pp,_Pg,_PX,_Pr,_PG,_Pq,_Pf,_PI,_PI,_PG,_PG,_Pd],_Qe=new T(function(){return B(unCStr("\u885b\u5175"));}),_Qf=function(_Qg,_){var _Qh=rMV(_Qg),_Qi=_Qh,_Qj=E(_Oq),_Qk=jsFind(_Qj);if(!_Qk[0]){return new F(function(){return _Bl(_Qj);});}else{var _Ql=new T(function(){var _Qm=B(_zD(_kV,E(E(_Qi)[7])[1]));if(!_Qm[0]){return [0];}else{var _Qn=_Qm[2],_Qo=function(_Qp){var _Qq=E(_Qp);if(!_Qq[0]){return [0];}else{var _Qr=_Qq[2],_Qs=new T(function(){return B(_Qo(_Qr));},1);return new F(function(){return _v(_Qq[1],_Qs);});}},_Qt=function(_Qu,_Qv){var _Qw=new T(function(){return B(_Qo(_Qv));},1);return new F(function(){return _v(_Qu,_Qw);});},_Qx=new T(function(){return B(_zL(_Qb,_Qn));});return B(_Qt(_Qm[1],_Qx));}}),_Qy=B(A(_k8,[_4b,_4Q,_Qk[1],_k7,_Ql,_])),_Qz=E(_Or),_QA=jsFind(_Qz);if(!_QA[0]){return new F(function(){return _Bl(_Qz);});}else{var _QB=E(_QA[1]),_QC=new T(function(){return B(_v(_Qc,_PL));}),_QD=jsQuerySelectorAll(_QB,toJSStr(B(unAppCStr("#character-detail-",_QC)))),_QE=function(_){var _QF=rMV(_Qg),_QG=E(_QF),_QH=_QG[7],_QI=new T(function(){var _QJ=E(_QH),_QK=_QJ[1],_QL=new T(function(){return B(_v(_QK,[1,_Qd,_11]));});return [0,_QL,_QJ[2],_QJ[3],_QJ[4]];}),_=wMV(_Qg,[0,_QG[1],_QG[2],_QG[3],_QG[4],_QG[5],_QG[6],_QI]);return new F(function(){return _Qf(_Qg,_);});},_QM=function(_QN,_){return new F(function(){return _QE(_);});},_QO=function(_QP,_){while(1){var _QQ=E(_QP);if(!_QQ[0]){return _eF;}else{var _QR=B(A(_pa,[_4R,_4b,_46,_QQ[1],_mh,_QM,_]));_QP=_QQ[2];continue;}}},_QS=function(_){var _QT=rMV(_Qg),_QU=E(_QT),_QV=_QU[7],_QW=new T(function(){var _QX=E(_QV),_QY=_QX[1],_QZ=new T(function(){return B(_Ph(_Oi,_Qd,_QY));});return [0,_QZ,_QX[2],_QX[3],_QX[4]];}),_=wMV(_Qg,[0,_QU[1],_QU[2],_QU[3],_QU[4],_QU[5],_QU[6],_QW]);return new F(function(){return _Qf(_Qg,_);});},_R0=function(_R1,_){return new F(function(){return _QS(_);});},_R2=function(_R3,_){while(1){var _R4=E(_R3);if(!_R4[0]){return _eF;}else{var _R5=B(A(_pa,[_4R,_4b,_46,_R4[1],_mh,_R0,_]));_R3=_R4[2];continue;}}},_R6=function(_R7){return new F(function(){return _Od(_Qc,E(_R7)[1]);});},_R8=function(_R9,_){while(1){var _Ra=(function(_Rb,_){var _Rc=E(_Rb);if(!_Rc[0]){return _eF;}else{var _Rd=_Rc[1],_Re=_Rc[2],_Rf=rMV(_Qg),_Rg=E(E(_Rf)[7])[1],_Rh=B(_Ps(_R6,_Rg));if(!_Rh[0]){if(B(_Ol(_Rg,0))<3){var _Ri=B(A(_k8,[_4b,_4Q,_Rd,_k7,_PQ,_])),_Rj=E(_PP),_Rk=jsQuerySelectorAll(E(_Rd),toJSStr(_Rj)),_Rl=B(_QO(_Rk,_)),_Rm=_Re,_=_;while(1){var _Rn=(function(_Ro,_){var _Rp=E(_Ro);if(!_Rp[0]){return _eF;}else{var _Rq=_Rp[1],_Rr=_Rp[2],_Rs=rMV(_Qg),_Rt=E(E(_Rs)[7])[1],_Ru=B(_Ps(_R6,_Rt));if(!_Ru[0]){if(B(_Ol(_Rt,0))<3){var _Rv=B(A(_k8,[_4b,_4Q,_Rq,_k7,_PQ,_])),_Rw=jsQuerySelectorAll(E(_Rq),toJSStr(_Rj)),_Rx=B(_QO(_Rw,_));_Rm=_Rr;return null;}else{var _Ry=B(A(_k8,[_4b,_4Q,_Rq,_k7,_PO,_]));_Rm=_Rr;return null;}}else{var _Rz=_Ru[1],_RA=new T(function(){var _RB=new T(function(){return B(_v(B(_H(0,E(_Rz),_11)),_PK));},1);return B(_v(_PN,_RB));}),_RC=B(A(_k8,[_4b,_4Q,_Rq,_k7,_RA,_])),_RD=jsQuerySelectorAll(E(_Rq),toJSStr(E(_PM))),_RE=B(_R2(_RD,_));_Rm=_Rr;return null;}}})(_Rm,_);if(_Rn!=null){return _Rn;}}}else{var _RF=B(A(_k8,[_4b,_4Q,_Rd,_k7,_PO,_]));_R9=_Re;return null;}}else{var _RG=_Rh[1],_RH=new T(function(){var _RI=new T(function(){return B(_v(B(_H(0,E(_RG),_11)),_PK));},1);return B(_v(_PN,_RI));}),_RJ=B(A(_k8,[_4b,_4Q,_Rd,_k7,_RH,_])),_RK=E(_PM),_RL=jsQuerySelectorAll(E(_Rd),toJSStr(_RK)),_RM=B(_R2(_RL,_)),_RN=_Re,_=_;while(1){var _RO=(function(_RP,_){var _RQ=E(_RP);if(!_RQ[0]){return _eF;}else{var _RR=_RQ[1],_RS=_RQ[2],_RT=rMV(_Qg),_RU=E(E(_RT)[7])[1],_RV=B(_Ps(_R6,_RU));if(!_RV[0]){if(B(_Ol(_RU,0))<3){var _RW=B(A(_k8,[_4b,_4Q,_RR,_k7,_PQ,_])),_RX=jsQuerySelectorAll(E(_RR),toJSStr(E(_PP))),_RY=B(_QO(_RX,_));_RN=_RS;return null;}else{var _RZ=B(A(_k8,[_4b,_4Q,_RR,_k7,_PO,_]));_RN=_RS;return null;}}else{var _S0=_RV[1],_S1=new T(function(){var _S2=new T(function(){return B(_v(B(_H(0,E(_S0),_11)),_PK));},1);return B(_v(_PN,_S2));}),_S3=B(A(_k8,[_4b,_4Q,_RR,_k7,_S1,_])),_S4=jsQuerySelectorAll(E(_RR),toJSStr(_RK)),_S5=B(_R2(_S4,_));_RN=_RS;return null;}}})(_RN,_);if(_RO!=null){return _RO;}}}}})(_R9,_);if(_Ra!=null){return _Ra;}}},_S6=B(_R8(_QD,_)),_S7=function(_S8,_){while(1){var _S9=(function(_Sa,_){var _Sb=E(_Sa);if(!_Sb[0]){return _eF;}else{var _Sc=_Sb[1],_Sd=new T(function(){return B(_v(E(_Sc)[1],_PL));}),_Se=jsQuerySelectorAll(_QB,toJSStr(B(unAppCStr("#character-detail-",_Sd)))),_Sf=function(_){var _Sg=rMV(_Qg),_Sh=E(_Sg),_Si=_Sh[7],_Sj=new T(function(){var _Sk=E(_Si),_Sl=_Sk[1],_Sm=new T(function(){return B(_v(_Sl,[1,_Sc,_11]));});return [0,_Sm,_Sk[2],_Sk[3],_Sk[4]];}),_=wMV(_Qg,[0,_Sh[1],_Sh[2],_Sh[3],_Sh[4],_Sh[5],_Sh[6],_Sj]);return new F(function(){return _Qf(_Qg,_);});},_Sn=function(_So,_){return new F(function(){return _Sf(_);});},_Sp=function(_Sq,_){while(1){var _Sr=E(_Sq);if(!_Sr[0]){return _eF;}else{var _Ss=B(A(_pa,[_4R,_4b,_46,_Sr[1],_mh,_Sn,_]));_Sq=_Sr[2];continue;}}},_St=function(_){var _Su=rMV(_Qg),_Sv=E(_Su),_Sw=_Sv[7],_Sx=new T(function(){var _Sy=E(_Sw),_Sz=_Sy[1],_SA=new T(function(){return B(_Ph(_Oi,_Sc,_Sz));});return [0,_SA,_Sy[2],_Sy[3],_Sy[4]];}),_=wMV(_Qg,[0,_Sv[1],_Sv[2],_Sv[3],_Sv[4],_Sv[5],_Sv[6],_Sx]);return new F(function(){return _Qf(_Qg,_);});},_SB=function(_SC,_){return new F(function(){return _St(_);});},_SD=function(_SE,_){while(1){var _SF=E(_SE);if(!_SF[0]){return _eF;}else{var _SG=B(A(_pa,[_4R,_4b,_46,_SF[1],_mh,_SB,_]));_SE=_SF[2];continue;}}},_SH=function(_tB){return new F(function(){return _Oi(_Sc,_tB);});},_SI=function(_SJ,_){while(1){var _SK=(function(_SL,_){var _SM=E(_SL);if(!_SM[0]){return _eF;}else{var _SN=_SM[1],_SO=_SM[2],_SP=rMV(_Qg),_SQ=E(E(_SP)[7])[1],_SR=B(_Ps(_SH,_SQ));if(!_SR[0]){if(B(_Ol(_SQ,0))<3){var _SS=B(A(_k8,[_4b,_4Q,_SN,_k7,_PQ,_])),_ST=E(_PP),_SU=jsQuerySelectorAll(E(_SN),toJSStr(_ST)),_SV=B(_Sp(_SU,_)),_SW=_SO,_=_;while(1){var _SX=(function(_SY,_){var _SZ=E(_SY);if(!_SZ[0]){return _eF;}else{var _T0=_SZ[1],_T1=_SZ[2],_T2=rMV(_Qg),_T3=E(E(_T2)[7])[1],_T4=B(_Ps(_SH,_T3));if(!_T4[0]){if(B(_Ol(_T3,0))<3){var _T5=B(A(_k8,[_4b,_4Q,_T0,_k7,_PQ,_])),_T6=jsQuerySelectorAll(E(_T0),toJSStr(_ST)),_T7=B(_Sp(_T6,_));_SW=_T1;return null;}else{var _T8=B(A(_k8,[_4b,_4Q,_T0,_k7,_PO,_]));_SW=_T1;return null;}}else{var _T9=_T4[1],_Ta=new T(function(){var _Tb=new T(function(){return B(_v(B(_H(0,E(_T9),_11)),_PK));},1);return B(_v(_PN,_Tb));}),_Tc=B(A(_k8,[_4b,_4Q,_T0,_k7,_Ta,_])),_Td=jsQuerySelectorAll(E(_T0),toJSStr(E(_PM))),_Te=B(_SD(_Td,_));_SW=_T1;return null;}}})(_SW,_);if(_SX!=null){return _SX;}}}else{var _Tf=B(A(_k8,[_4b,_4Q,_SN,_k7,_PO,_]));_SJ=_SO;return null;}}else{var _Tg=_SR[1],_Th=new T(function(){var _Ti=new T(function(){return B(_v(B(_H(0,E(_Tg),_11)),_PK));},1);return B(_v(_PN,_Ti));}),_Tj=B(A(_k8,[_4b,_4Q,_SN,_k7,_Th,_])),_Tk=E(_PM),_Tl=jsQuerySelectorAll(E(_SN),toJSStr(_Tk)),_Tm=B(_SD(_Tl,_)),_Tn=_SO,_=_;while(1){var _To=(function(_Tp,_){var _Tq=E(_Tp);if(!_Tq[0]){return _eF;}else{var _Tr=_Tq[1],_Ts=_Tq[2],_Tt=rMV(_Qg),_Tu=E(E(_Tt)[7])[1],_Tv=B(_Ps(_SH,_Tu));if(!_Tv[0]){if(B(_Ol(_Tu,0))<3){var _Tw=B(A(_k8,[_4b,_4Q,_Tr,_k7,_PQ,_])),_Tx=jsQuerySelectorAll(E(_Tr),toJSStr(E(_PP))),_Ty=B(_Sp(_Tx,_));_Tn=_Ts;return null;}else{var _Tz=B(A(_k8,[_4b,_4Q,_Tr,_k7,_PO,_]));_Tn=_Ts;return null;}}else{var _TA=_Tv[1],_TB=new T(function(){var _TC=new T(function(){return B(_v(B(_H(0,E(_TA),_11)),_PK));},1);return B(_v(_PN,_TC));}),_TD=B(A(_k8,[_4b,_4Q,_Tr,_k7,_TB,_])),_TE=jsQuerySelectorAll(E(_Tr),toJSStr(_Tk)),_TF=B(_SD(_TE,_));_Tn=_Ts;return null;}}})(_Tn,_);if(_To!=null){return _To;}}}}})(_SJ,_);if(_SK!=null){return _SK;}}},_TG=B(_SI(_Se,_));_S8=_Sb[2];return null;}})(_S8,_);if(_S9!=null){return _S9;}}},_TH=_Qe,_TI=_Qa,_=_,_TJ=new T(function(){return B(_v(_TH,_PL));}),_TK=jsQuerySelectorAll(_QB,toJSStr(B(unAppCStr("#character-detail-",_TJ)))),_TL=function(_){var _TM=rMV(_Qg),_TN=E(_TM),_TO=_TN[7],_TP=new T(function(){var _TQ=E(_TO),_TR=_TQ[1],_TS=new T(function(){return B(_v(_TR,[1,[0,_TH,_PH,_PG,_Pr,_PI,_Pe,_Pp,_Pf,_Pg,_Pg,_Pq,_Pq,_Pd],_11]));});return [0,_TS,_TQ[2],_TQ[3],_TQ[4]];}),_=wMV(_Qg,[0,_TN[1],_TN[2],_TN[3],_TN[4],_TN[5],_TN[6],_TP]);return new F(function(){return _Qf(_Qg,_);});},_TT=function(_TU,_){return new F(function(){return _TL(_);});},_TV=function(_TW,_){while(1){var _TX=E(_TW);if(!_TX[0]){return _eF;}else{var _TY=B(A(_pa,[_4R,_4b,_46,_TX[1],_mh,_TT,_]));_TW=_TX[2];continue;}}},_TZ=function(_){var _U0=rMV(_Qg),_U1=E(_U0),_U2=_U1[7],_U3=new T(function(){var _U4=E(_U2),_U5=_U4[1],_U6=new T(function(){return B(_Ph(_Oi,[0,_TH,_PH,_PG,_Pr,_PI,_Pe,_Pp,_Pf,_Pg,_Pg,_Pq,_Pq,_Pd],_U5));});return [0,_U6,_U4[2],_U4[3],_U4[4]];}),_=wMV(_Qg,[0,_U1[1],_U1[2],_U1[3],_U1[4],_U1[5],_U1[6],_U3]);return new F(function(){return _Qf(_Qg,_);});},_U7=function(_U8,_){return new F(function(){return _TZ(_);});},_U9=function(_Ua,_){while(1){var _Ub=E(_Ua);if(!_Ub[0]){return _eF;}else{var _Uc=B(A(_pa,[_4R,_4b,_46,_Ub[1],_mh,_U7,_]));_Ua=_Ub[2];continue;}}},_Ud=function(_Ue){return new F(function(){return _Od(_TH,E(_Ue)[1]);});},_Uf=function(_Ug,_){while(1){var _Uh=(function(_Ui,_){var _Uj=E(_Ui);if(!_Uj[0]){return _eF;}else{var _Uk=_Uj[1],_Ul=_Uj[2],_Um=rMV(_Qg),_Un=E(E(_Um)[7])[1],_Uo=B(_Ps(_Ud,_Un));if(!_Uo[0]){if(B(_Ol(_Un,0))<3){var _Up=B(A(_k8,[_4b,_4Q,_Uk,_k7,_PQ,_])),_Uq=E(_PP),_Ur=jsQuerySelectorAll(E(_Uk),toJSStr(_Uq)),_Us=B(_TV(_Ur,_)),_Ut=_Ul,_=_;while(1){var _Uu=(function(_Uv,_){var _Uw=E(_Uv);if(!_Uw[0]){return _eF;}else{var _Ux=_Uw[1],_Uy=_Uw[2],_Uz=rMV(_Qg),_UA=E(E(_Uz)[7])[1],_UB=B(_Ps(_Ud,_UA));if(!_UB[0]){if(B(_Ol(_UA,0))<3){var _UC=B(A(_k8,[_4b,_4Q,_Ux,_k7,_PQ,_])),_UD=jsQuerySelectorAll(E(_Ux),toJSStr(_Uq)),_UE=B(_TV(_UD,_));_Ut=_Uy;return null;}else{var _UF=B(A(_k8,[_4b,_4Q,_Ux,_k7,_PO,_]));_Ut=_Uy;return null;}}else{var _UG=_UB[1],_UH=new T(function(){var _UI=new T(function(){return B(_v(B(_H(0,E(_UG),_11)),_PK));},1);return B(_v(_PN,_UI));}),_UJ=B(A(_k8,[_4b,_4Q,_Ux,_k7,_UH,_])),_UK=jsQuerySelectorAll(E(_Ux),toJSStr(E(_PM))),_UL=B(_U9(_UK,_));_Ut=_Uy;return null;}}})(_Ut,_);if(_Uu!=null){return _Uu;}}}else{var _UM=B(A(_k8,[_4b,_4Q,_Uk,_k7,_PO,_]));_Ug=_Ul;return null;}}else{var _UN=_Uo[1],_UO=new T(function(){var _UP=new T(function(){return B(_v(B(_H(0,E(_UN),_11)),_PK));},1);return B(_v(_PN,_UP));}),_UQ=B(A(_k8,[_4b,_4Q,_Uk,_k7,_UO,_])),_UR=E(_PM),_US=jsQuerySelectorAll(E(_Uk),toJSStr(_UR)),_UT=B(_U9(_US,_)),_UU=_Ul,_=_;while(1){var _UV=(function(_UW,_){var _UX=E(_UW);if(!_UX[0]){return _eF;}else{var _UY=_UX[1],_UZ=_UX[2],_V0=rMV(_Qg),_V1=E(E(_V0)[7])[1],_V2=B(_Ps(_Ud,_V1));if(!_V2[0]){if(B(_Ol(_V1,0))<3){var _V3=B(A(_k8,[_4b,_4Q,_UY,_k7,_PQ,_])),_V4=jsQuerySelectorAll(E(_UY),toJSStr(E(_PP))),_V5=B(_TV(_V4,_));_UU=_UZ;return null;}else{var _V6=B(A(_k8,[_4b,_4Q,_UY,_k7,_PO,_]));_UU=_UZ;return null;}}else{var _V7=_V2[1],_V8=new T(function(){var _V9=new T(function(){return B(_v(B(_H(0,E(_V7),_11)),_PK));},1);return B(_v(_PN,_V9));}),_Va=B(A(_k8,[_4b,_4Q,_UY,_k7,_V8,_])),_Vb=jsQuerySelectorAll(E(_UY),toJSStr(_UR)),_Vc=B(_U9(_Vb,_));_UU=_UZ;return null;}}})(_UU,_);if(_UV!=null){return _UV;}}}}})(_Ug,_);if(_Uh!=null){return _Uh;}}},_Vd=B(_Uf(_TK,_));return new F(function(){return _S7(_TI,_);});}}},_Ve=false,_Vf=0,_Vg=1,_Vh=true,_Vi=function(_){return _eF;},_Vj=function(_Vk,_Vl){while(1){var _Vm=E(_Vl);if(!_Vm[0]){return [0];}else{var _Vn=_Vm[2],_Vo=E(_Vk);if(_Vo==1){return E(_Vn);}else{_Vk=_Vo-1|0;_Vl=_Vn;continue;}}}},_Vp=function(_Vq,_Vr,_Vs){var _Vt=E(_Vq);if(_Vt==1){return E(_Vs);}else{return new F(function(){return _Vj(_Vt-1|0,_Vs);});}},_Vu=function(_Vv,_Vw){var _Vx=E(_Vw);if(!_Vx[0]){return [0];}else{var _Vy=_Vx[1],_Vz=_Vx[2],_VA=E(_Vv);if(_VA==1){return [1,_Vy,_11];}else{var _VB=new T(function(){return B(_Vu(_VA-1|0,_Vz));});return [1,_Vy,_VB];}}},_VC=function(_VD,_VE,_VF){var _VG=new T(function(){if(_VD>0){return B(_VH(_VD,B(_Vp(_VD,_VE,_VF))));}else{return B(_VC(_VD,_VE,_VF));}}),_VI=new T(function(){if(0>=_VD){return [0];}else{return B(_Vu(_VD,[1,_VE,_VF]));}});return [1,_VI,_VG];},_VH=function(_VJ,_VK){var _VL=E(_VK);if(!_VL[0]){return [0];}else{var _VM=_VL[1],_VN=_VL[2],_VO=new T(function(){if(_VJ>0){return B(_VH(_VJ,B(_Vp(_VJ,_VM,_VN))));}else{return B(_VC(_VJ,_VM,_VN));}}),_VP=new T(function(){if(0>=_VJ){return [0];}else{return B(_Vu(_VJ,_VL));}});return [1,_VP,_VO];}},_VQ=function(_VR,_VS,_VT,_VU){var _VV=E(_VU);if(!_VV[0]){var _VW=_VV[3],_VX=_VV[4],_VY=_VV[5],_VZ=E(_VV[2]),_W0=E(_VR),_W1=E(_VZ[1]);if(_W0>=_W1){if(_W0!=_W1){return new F(function(){return _5E(_VZ,_VW,_VX,B(_VQ(_W0,_VS,_VT,_VY)));});}else{var _W2=E(_VS),_W3=E(_VZ[2]);if(_W2>=_W3){if(_W2!=_W3){return new F(function(){return _5E(_VZ,_VW,_VX,B(_VQ(_W0,_W2,_VT,_VY)));});}else{return [0,_VV[1],[0,_W0,_W2],_VT,E(_VX),E(_VY)];}}else{return new F(function(){return _6x(_VZ,_VW,B(_VQ(_W0,_W2,_VT,_VX)),_VY);});}}}else{return new F(function(){return _6x(_VZ,_VW,B(_VQ(_W0,_VS,_VT,_VX)),_VY);});}}else{return [0,1,[0,_VR,_VS],_VT,E(_5z),E(_5z)];}},_W4=function(_W5){var _W6=E(_W5);if(!_W6[0]){return [0];}else{var _W7=_W6[2],_W8=new T(function(){return B(_W4(_W7));},1);return new F(function(){return _v(_W6[1],_W8);});}},_W9=function(_Wa){return new F(function(){return _W4(_Wa);});},_Wb=(function(s){return s[0];}),_Wc=function(_Wd,_We){var _Wf=_Wd%_We;if(_Wd<=0){if(_Wd>=0){return E(_Wf);}else{if(_We<=0){return E(_Wf);}else{var _Wg=E(_Wf);return (_Wg==0)?0:_Wg+_We|0;}}}else{if(_We>=0){if(_Wd>=0){return E(_Wf);}else{if(_We<=0){return E(_Wf);}else{var _Wh=E(_Wf);return (_Wh==0)?0:_Wh+_We|0;}}}else{var _Wi=E(_Wf);return (_Wi==0)?0:_Wi+_We|0;}}},_Wj=(function(s){var ba = window['newByteArr'](16);ba['v']['w32'][0] = s[0];ba['v']['w32'][1] = s[1];ba['v']['w32'][2] = s[2];ba['v']['w32'][3] = s[3];return window['md51'](ba,16);}),_Wk=function(_Wl){var _Wm=function(_){return new F(function(){return E(_Wj)(E(_Wl));});};return new F(function(){return _3v(_Wm);});},_Wn=function(_Wo,_Wp,_Wq){while(1){var _Wr=(function(_Ws,_Wt,_Wu){if(_Ws>_Wt){var _Wv=_Wt,_Ww=_Ws,_Wx=_Wu;_Wo=_Wv;_Wp=_Ww;_Wq=_Wx;return null;}else{var _Wy=new T(function(){return B(_Wk(_Wu));}),_Wz=new T(function(){var _WA=(_Wt-_Ws|0)+1|0;switch(_WA){case -1:return _Ws;break;case 0:return E(_jg);break;default:var _WB=function(_){var _WC=E(_Wb)(E(_Wu));return new F(function(){return _1e(_WC,0);});};return B(_Wc(B(_3v(_WB)),_WA))+_Ws|0;}});return [0,_Wz,_Wy];}})(_Wo,_Wp,_Wq);if(_Wr!=null){return _Wr;}}},_WD=(function(){var ba = window['newByteArr'](16);ba['v']['f64'][0] = Math.random();ba['v']['f64'][1] = Math.random();return window['md51'](ba,16);}),_WE=function(_WF,_){while(1){var _WG=(function(_WH,_){var _WI=E(_WH);if(!_WI[0]){return _11;}else{var _WJ=_WI[2],_WK=E(_WI[1]);if(!_WK[0]){_WF=_WJ;return null;}else{var _WL=_WK[2],_WM=E(_WK[1]),_WN=E(_WM[1]),_WO=E(_WM[2]),_WP=E(_WD),_WQ=_WP(),_WR=_WQ,_WS=E(_WO[2]),_WT=E(_WN[2]);if((_WS-_WT|0)<4){var _WU=function(_WV,_){var _WW=E(_WV);if(!_WW[0]){return new F(function(){return _WE(_WJ,_);});}else{var _WX=_WW[2],_WY=E(_WW[1]),_WZ=E(_WY[1]),_X0=E(_WY[2]),_X1=_WP(),_X2=_X1,_X3=E(_X0[2]),_X4=E(_WZ[2]);if((_X3-_X4|0)<4){var _X5=B(_WU(_WX,_));return [1,_11,_X5];}else{var _X6=B(_WU(_WX,_)),_X7=new T(function(){return E(B(_Wn((_X4+2|0)+1|0,(_X3-2|0)-1|0,_X2))[1]);});return [1,[1,[0,_WZ,[0,_X0[1],_X7]],[1,[0,[0,_WZ[1],_X7],_X0],_11]],_X6];}}},_X8=B(_WU(_WL,_));return [1,_11,_X8];}else{var _X9=function(_Xa,_){var _Xb=E(_Xa);if(!_Xb[0]){return new F(function(){return _WE(_WJ,_);});}else{var _Xc=_Xb[2],_Xd=E(_Xb[1]),_Xe=E(_Xd[1]),_Xf=E(_Xd[2]),_Xg=_WP(),_Xh=_Xg,_Xi=E(_Xf[2]),_Xj=E(_Xe[2]);if((_Xi-_Xj|0)<4){var _Xk=B(_X9(_Xc,_));return [1,_11,_Xk];}else{var _Xl=B(_X9(_Xc,_)),_Xm=new T(function(){return E(B(_Wn((_Xj+2|0)+1|0,(_Xi-2|0)-1|0,_Xh))[1]);});return [1,[1,[0,_Xe,[0,_Xf[1],_Xm]],[1,[0,[0,_Xe[1],_Xm],_Xf],_11]],_Xl];}}},_Xn=B(_X9(_WL,_)),_Xo=new T(function(){return E(B(_Wn((_WT+2|0)+1|0,(_WS-2|0)-1|0,_WR))[1]);});return [1,[1,[0,_WN,[0,_WO[1],_Xo]],[1,[0,[0,_WN[1],_Xo],_WO],_11]],_Xn];}}}})(_WF,_);if(_WG!=null){return _WG;}}},_Xp=function(_Xq,_){var _Xr=E(_Xq);if(!_Xr[0]){return _11;}else{var _Xs=_Xr[2],_Xt=E(_Xr[1]),_Xu=E(_Xt[1]),_Xv=E(_Xt[2]),_Xw=E(_WD),_Xx=_Xw(),_Xy=_Xx,_Xz=E(_Xv[1]),_XA=E(_Xu[1]);if((_Xz-_XA|0)<4){var _XB=function(_XC,_){var _XD=E(_XC);if(!_XD[0]){return _11;}else{var _XE=_XD[2],_XF=E(_XD[1]),_XG=E(_XF[1]),_XH=E(_XF[2]),_XI=_Xw(),_XJ=_XI,_XK=E(_XH[1]),_XL=E(_XG[1]);if((_XK-_XL|0)<4){var _XM=B(_XB(_XE,_));return [1,_11,_XM];}else{var _XN=B(_XB(_XE,_)),_XO=new T(function(){return E(B(_Wn((_XL+2|0)+1|0,(_XK-2|0)-1|0,_XJ))[1]);});return [1,[1,[0,_XG,[0,_XO,_XH[2]]],[1,[0,[0,_XO,_XG[2]],_XH],_11]],_XN];}}},_XP=B(_XB(_Xs,_));return [1,_11,_XP];}else{var _XQ=function(_XR,_){var _XS=E(_XR);if(!_XS[0]){return _11;}else{var _XT=_XS[2],_XU=E(_XS[1]),_XV=E(_XU[1]),_XW=E(_XU[2]),_XX=_Xw(),_XY=_XX,_XZ=E(_XW[1]),_Y0=E(_XV[1]);if((_XZ-_Y0|0)<4){var _Y1=B(_XQ(_XT,_));return [1,_11,_Y1];}else{var _Y2=B(_XQ(_XT,_)),_Y3=new T(function(){return E(B(_Wn((_Y0+2|0)+1|0,(_XZ-2|0)-1|0,_XY))[1]);});return [1,[1,[0,_XV,[0,_Y3,_XW[2]]],[1,[0,[0,_Y3,_XV[2]],_XW],_11]],_Y2];}}},_Y4=B(_XQ(_Xs,_)),_Y5=new T(function(){return E(B(_Wn((_XA+2|0)+1|0,(_Xz-2|0)-1|0,_Xy))[1]);});return [1,[1,[0,_Xu,[0,_Y5,_Xv[2]]],[1,[0,[0,_Y5,_Xu[2]],_Xv],_11]],_Y4];}}},_Y6=0,_Y7=[0,_Y6,_Y6],_Y8=34,_Y9=44,_Ya=[0,_Y9,_Y8],_Yb=[0,_Y7,_Ya],_Yc=[1,_Yb,_11],_Yd=function(_Ye,_){var _Yf=E(_Ye);if(_Yf==1){var _Yg=B(_Xp(_Yc,_)),_Yh=B(_WE(_Yg,_)),_Yi=_Yh;return new T(function(){return B(_W9(_Yi));});}else{var _Yj=B(_Yd(_Yf+1|0,_)),_Yk=B(_Xp(_Yj,_)),_Yl=B(_WE(_Yk,_)),_Ym=_Yl;return new T(function(){return B(_W9(_Ym));});}},_Yn=function(_Yo,_){var _Yp=E(_Yo);if(!_Yp[0]){return _11;}else{var _Yq=_Yp[2],_Yr=E(_Yp[1]),_Ys=E(_Yr[1]),_Yt=E(_Yr[2]),_Yu=E(_WD),_Yv=_Yu(),_Yw=_Yv,_Yx=_Yu(),_Yy=_Yx,_Yz=_Yu(),_YA=_Yz,_YB=_Yu(),_YC=_YB,_YD=E(_Ys[1]),_YE=E(_Yt[1]);if((_YD+1|0)>(_YE-2|0)){var _YF=function(_YG,_){while(1){var _YH=(function(_YI,_){var _YJ=E(_YI);if(!_YJ[0]){return _11;}else{var _YK=_YJ[2],_YL=E(_YJ[1]),_YM=E(_YL[1]),_YN=E(_YL[2]),_YO=_Yu(),_YP=_YO,_YQ=_Yu(),_YR=_YQ,_YS=_Yu(),_YT=_YS,_YU=_Yu(),_YV=_YU,_YW=E(_YM[1]),_YX=E(_YN[1]);if((_YW+1|0)>(_YX-2|0)){_YG=_YK;return null;}else{var _YY=E(_YM[2]),_YZ=E(_YN[2]);if((_YY+1|0)>(_YZ-2|0)){_YG=_YK;return null;}else{var _Z0=B(_YF(_YK,_)),_Z1=new T(function(){return E(B(_Wn(_YW+1|0,_YX-2|0,_YP))[1]);}),_Z2=new T(function(){return E(B(_Wn(_YY+1|0,_YZ-2|0,_YT))[1]);}),_Z3=new T(function(){return E(B(_Wn((E(_Z2)+2|0)-1|0,_YZ-1|0,_YV))[1]);}),_Z4=new T(function(){return E(B(_Wn((E(_Z1)+2|0)-1|0,_YX-1|0,_YR))[1]);});return [1,[0,[0,_Z1,_Z2],[0,_Z4,_Z3]],_Z0];}}}})(_YG,_);if(_YH!=null){return _YH;}}};return new F(function(){return _YF(_Yq,_);});}else{var _Z5=E(_Ys[2]),_Z6=E(_Yt[2]);if((_Z5+1|0)>(_Z6-2|0)){var _Z7=function(_Z8,_){while(1){var _Z9=(function(_Za,_){var _Zb=E(_Za);if(!_Zb[0]){return _11;}else{var _Zc=_Zb[2],_Zd=E(_Zb[1]),_Ze=E(_Zd[1]),_Zf=E(_Zd[2]),_Zg=_Yu(),_Zh=_Zg,_Zi=_Yu(),_Zj=_Zi,_Zk=_Yu(),_Zl=_Zk,_Zm=_Yu(),_Zn=_Zm,_Zo=E(_Ze[1]),_Zp=E(_Zf[1]);if((_Zo+1|0)>(_Zp-2|0)){_Z8=_Zc;return null;}else{var _Zq=E(_Ze[2]),_Zr=E(_Zf[2]);if((_Zq+1|0)>(_Zr-2|0)){_Z8=_Zc;return null;}else{var _Zs=B(_Z7(_Zc,_)),_Zt=new T(function(){return E(B(_Wn(_Zo+1|0,_Zp-2|0,_Zh))[1]);}),_Zu=new T(function(){return E(B(_Wn(_Zq+1|0,_Zr-2|0,_Zl))[1]);}),_Zv=new T(function(){return E(B(_Wn((E(_Zu)+2|0)-1|0,_Zr-1|0,_Zn))[1]);}),_Zw=new T(function(){return E(B(_Wn((E(_Zt)+2|0)-1|0,_Zp-1|0,_Zj))[1]);});return [1,[0,[0,_Zt,_Zu],[0,_Zw,_Zv]],_Zs];}}}})(_Z8,_);if(_Z9!=null){return _Z9;}}};return new F(function(){return _Z7(_Yq,_);});}else{var _Zx=function(_Zy,_){while(1){var _Zz=(function(_ZA,_){var _ZB=E(_ZA);if(!_ZB[0]){return _11;}else{var _ZC=_ZB[2],_ZD=E(_ZB[1]),_ZE=E(_ZD[1]),_ZF=E(_ZD[2]),_ZG=_Yu(),_ZH=_ZG,_ZI=_Yu(),_ZJ=_ZI,_ZK=_Yu(),_ZL=_ZK,_ZM=_Yu(),_ZN=_ZM,_ZO=E(_ZE[1]),_ZP=E(_ZF[1]);if((_ZO+1|0)>(_ZP-2|0)){_Zy=_ZC;return null;}else{var _ZQ=E(_ZE[2]),_ZR=E(_ZF[2]);if((_ZQ+1|0)>(_ZR-2|0)){_Zy=_ZC;return null;}else{var _ZS=B(_Zx(_ZC,_)),_ZT=new T(function(){return E(B(_Wn(_ZO+1|0,_ZP-2|0,_ZH))[1]);}),_ZU=new T(function(){return E(B(_Wn(_ZQ+1|0,_ZR-2|0,_ZL))[1]);}),_ZV=new T(function(){return E(B(_Wn((E(_ZU)+2|0)-1|0,_ZR-1|0,_ZN))[1]);}),_ZW=new T(function(){return E(B(_Wn((E(_ZT)+2|0)-1|0,_ZP-1|0,_ZJ))[1]);});return [1,[0,[0,_ZT,_ZU],[0,_ZW,_ZV]],_ZS];}}}})(_Zy,_);if(_Zz!=null){return _Zz;}}},_ZX=B(_Zx(_Yq,_)),_ZY=new T(function(){return E(B(_Wn(_YD+1|0,_YE-2|0,_Yw))[1]);}),_ZZ=new T(function(){return E(B(_Wn(_Z5+1|0,_Z6-2|0,_YA))[1]);}),_100=new T(function(){return E(B(_Wn((E(_ZZ)+2|0)-1|0,_Z6-1|0,_YC))[1]);}),_101=new T(function(){return E(B(_Wn((E(_ZY)+2|0)-1|0,_YE-1|0,_Yy))[1]);});return [1,[0,[0,_ZY,_ZZ],[0,_101,_100]],_ZX];}}}},_102=function(_103,_104,_){var _105=E(_103);if(!_105[0]){return _11;}else{var _106=_105[2],_107=E(_104);if(!_107[0]){return _11;}else{var _108=_107[2],_109=E(_105[1]),_10a=E(_109[2]),_10b=E(_107[1]),_10c=E(_10b[1]),_10d=_10c[1],_10e=E(_10b[2])[1],_10f=E(E(_109[1])[2]);if(!E(_10f)){var _10g=B(_102(_106,_108,_));return [1,_11,_10g];}else{var _10h=E(_WD),_10i=_10h(),_10j=_10i,_10k=function(_10l,_10m,_){var _10n=E(_10l);if(!_10n[0]){return _11;}else{var _10o=_10n[2],_10p=E(_10m);if(!_10p[0]){return _11;}else{var _10q=_10p[2],_10r=E(_10n[1]),_10s=E(_10r[2]),_10t=E(_10p[1]),_10u=E(_10t[1]),_10v=_10u[1],_10w=E(_10t[2])[1],_10x=E(E(_10r[1])[2]);if(!E(_10x)){var _10y=B(_10k(_10o,_10q,_));return [1,_11,_10y];}else{var _10z=_10h(),_10A=_10z,_10B=B(_10k(_10o,_10q,_)),_10C=new T(function(){return E(B(_Wn(E(_10v),E(_10w),_10A))[1]);});return [1,[1,[0,[0,[0,_10C,_10x],[0,_10C,_10u[2]]],[0,_10C,_10x]],_11],_10B];}}}},_10D=B(_10k(_106,_108,_)),_10E=new T(function(){return E(B(_Wn(E(_10d),E(_10e),_10j))[1]);});return [1,[1,[0,[0,[0,_10E,_10f],[0,_10E,_10c[2]]],[0,_10E,_10f]],_11],_10D];}}}},_10F=function(_10G,_10H,_){var _10I=E(_10G);if(!_10I[0]){return _11;}else{var _10J=_10I[2],_10K=E(_10H);if(!_10K[0]){return _11;}else{var _10L=_10K[2],_10M=E(_10I[1]),_10N=E(_10M[1]),_10O=E(_10K[1]),_10P=E(_10O[1])[1],_10Q=E(_10O[2]),_10R=_10Q[1],_10S=E(E(_10M[2])[2]);if(E(_10S)==34){var _10T=B(_10F(_10J,_10L,_));return [1,_11,_10T];}else{var _10U=E(_WD),_10V=_10U(),_10W=_10V,_10X=function(_10Y,_10Z,_){var _110=E(_10Y);if(!_110[0]){return _11;}else{var _111=_110[2],_112=E(_10Z);if(!_112[0]){return _11;}else{var _113=_112[2],_114=E(_110[1]),_115=E(_114[1]),_116=E(_112[1]),_117=E(_116[1])[1],_118=E(_116[2]),_119=_118[1],_11a=E(E(_114[2])[2]);if(E(_11a)==34){var _11b=B(_10X(_111,_113,_));return [1,_11,_11b];}else{var _11c=_10U(),_11d=_11c,_11e=B(_10X(_111,_113,_)),_11f=new T(function(){return E(B(_Wn(E(_117),E(_119),_11d))[1]);});return [1,[1,[0,[0,[0,_11f,_118[2]],[0,_11f,_11a]],[0,_11f,_11a]],_11],_11e];}}}},_11g=B(_10X(_10J,_10L,_)),_11h=new T(function(){return E(B(_Wn(E(_10P),E(_10R),_10W))[1]);});return [1,[1,[0,[0,[0,_11h,_10Q[2]],[0,_11h,_10S]],[0,_11h,_10S]],_11],_11g];}}}},_11i=function(_11j,_11k,_){var _11l=E(_11j);if(!_11l[0]){return _11;}else{var _11m=_11l[2],_11n=E(_11k);if(!_11n[0]){return _11;}else{var _11o=_11n[2],_11p=E(_11l[1]),_11q=E(_11p[2]),_11r=E(_11n[1]),_11s=E(_11r[1]),_11t=_11s[2],_11u=E(_11r[2])[2],_11v=E(E(_11p[1])[1]);if(!E(_11v)){var _11w=B(_11i(_11m,_11o,_));return [1,_11,_11w];}else{var _11x=E(_WD),_11y=_11x(),_11z=_11y,_11A=function(_11B,_11C,_){var _11D=E(_11B);if(!_11D[0]){return _11;}else{var _11E=_11D[2],_11F=E(_11C);if(!_11F[0]){return _11;}else{var _11G=_11F[2],_11H=E(_11D[1]),_11I=E(_11H[2]),_11J=E(_11F[1]),_11K=E(_11J[1]),_11L=_11K[2],_11M=E(_11J[2])[2],_11N=E(E(_11H[1])[1]);if(!E(_11N)){var _11O=B(_11A(_11E,_11G,_));return [1,_11,_11O];}else{var _11P=_11x(),_11Q=_11P,_11R=B(_11A(_11E,_11G,_)),_11S=new T(function(){return E(B(_Wn(E(_11L),E(_11M),_11Q))[1]);});return [1,[1,[0,[0,[0,_11N,_11S],[0,_11K[1],_11S]],[0,_11N,_11S]],_11],_11R];}}}},_11T=B(_11A(_11m,_11o,_)),_11U=new T(function(){return E(B(_Wn(E(_11t),E(_11u),_11z))[1]);});return [1,[1,[0,[0,[0,_11v,_11U],[0,_11s[1],_11U]],[0,_11v,_11U]],_11],_11T];}}}},_11V=function(_11W,_11X,_){var _11Y=E(_11W);if(!_11Y[0]){return _11;}else{var _11Z=_11Y[2],_120=E(_11X);if(!_120[0]){return _11;}else{var _121=_120[2],_122=E(_11Y[1]),_123=E(_122[1]),_124=E(_120[1]),_125=E(_124[1])[2],_126=E(_124[2]),_127=_126[2],_128=E(E(_122[2])[1]);if(E(_128)==44){var _129=B(_11V(_11Z,_121,_));return [1,_11,_129];}else{var _12a=E(_WD),_12b=_12a(),_12c=_12b,_12d=function(_12e,_12f,_){var _12g=E(_12e);if(!_12g[0]){return _11;}else{var _12h=_12g[2],_12i=E(_12f);if(!_12i[0]){return _11;}else{var _12j=_12i[2],_12k=E(_12g[1]),_12l=E(_12k[1]),_12m=E(_12i[1]),_12n=E(_12m[1])[2],_12o=E(_12m[2]),_12p=_12o[2],_12q=E(E(_12k[2])[1]);if(E(_12q)==44){var _12r=B(_12d(_12h,_12j,_));return [1,_11,_12r];}else{var _12s=_12a(),_12t=_12s,_12u=B(_12d(_12h,_12j,_)),_12v=new T(function(){return E(B(_Wn(E(_12n),E(_12p),_12t))[1]);});return [1,[1,[0,[0,[0,_12o[1],_12v],[0,_12q,_12v]],[0,_12q,_12v]],_11],_12u];}}}},_12w=B(_12d(_11Z,_121,_)),_12x=new T(function(){return E(B(_Wn(E(_125),E(_127),_12c))[1]);});return [1,[1,[0,[0,[0,_126[1],_12x],[0,_128,_12x]],[0,_128,_12x]],_11],_12w];}}}},_12y=function(_12z,_12A,_12B,_12C,_12D){var _12E=E(_12z);if(_12E==1){var _12F=E(_12D);if(!_12F[0]){return [0,[0,1,[0,_12A,_12B],_12C,E(_5z),E(_5z)],_11,_11];}else{var _12G=E(E(_12F[1])[1]),_12H=E(_12G[1]);return (_12A>=_12H)?(_12A!=_12H)?[0,[0,1,[0,_12A,_12B],_12C,E(_5z),E(_5z)],_11,_12F]:(_12B<E(_12G[2]))?[0,[0,1,[0,_12A,_12B],_12C,E(_5z),E(_5z)],_12F,_11]:[0,[0,1,[0,_12A,_12B],_12C,E(_5z),E(_5z)],_11,_12F]:[0,[0,1,[0,_12A,_12B],_12C,E(_5z),E(_5z)],_12F,_11];}}else{var _12I=B(_12y(_12E>>1,_12A,_12B,_12C,_12D)),_12J=_12I[1],_12K=_12I[3],_12L=E(_12I[2]);if(!_12L[0]){return [0,_12J,_11,_12K];}else{var _12M=E(_12L[1]),_12N=_12M[1],_12O=_12M[2],_12P=E(_12L[2]);if(!_12P[0]){var _12Q=new T(function(){return B(_6o(_12N,_12O,_12J));});return [0,_12Q,_11,_12K];}else{var _12R=_12P[2],_12S=E(_12P[1]),_12T=_12S[2],_12U=E(_12N),_12V=E(_12S[1]),_12W=_12V[2],_12X=E(_12U[1]),_12Y=E(_12V[1]);if(_12X>=_12Y){if(_12X!=_12Y){return [0,_12J,_11,_12L];}else{var _12Z=E(_12W);if(E(_12U[2])<_12Z){var _130=B(_12y(_12E>>1,_12Y,_12Z,_12T,_12R)),_131=_130[1],_132=new T(function(){return B(_7T(_12U,_12O,_12J,_131));});return [0,_132,_130[2],_130[3]];}else{return [0,_12J,_11,_12L];}}}else{var _133=B(_134(_12E>>1,_12Y,_12W,_12T,_12R)),_135=_133[1],_136=new T(function(){return B(_7T(_12U,_12O,_12J,_135));});return [0,_136,_133[2],_133[3]];}}}}},_134=function(_137,_138,_139,_13a,_13b){var _13c=E(_137);if(_13c==1){var _13d=E(_13b);if(!_13d[0]){return [0,[0,1,[0,_138,_139],_13a,E(_5z),E(_5z)],_11,_11];}else{var _13e=E(E(_13d[1])[1]),_13f=E(_13e[1]);if(_138>=_13f){if(_138!=_13f){return [0,[0,1,[0,_138,_139],_13a,E(_5z),E(_5z)],_11,_13d];}else{var _13g=E(_139);return (_13g<E(_13e[2]))?[0,[0,1,[0,_138,_13g],_13a,E(_5z),E(_5z)],_13d,_11]:[0,[0,1,[0,_138,_13g],_13a,E(_5z),E(_5z)],_11,_13d];}}else{return [0,[0,1,[0,_138,_139],_13a,E(_5z),E(_5z)],_13d,_11];}}}else{var _13h=B(_134(_13c>>1,_138,_139,_13a,_13b)),_13i=_13h[1],_13j=_13h[3],_13k=E(_13h[2]);if(!_13k[0]){return [0,_13i,_11,_13j];}else{var _13l=E(_13k[1]),_13m=_13l[1],_13n=_13l[2],_13o=E(_13k[2]);if(!_13o[0]){var _13p=new T(function(){return B(_6o(_13m,_13n,_13i));});return [0,_13p,_11,_13j];}else{var _13q=_13o[2],_13r=E(_13o[1]),_13s=_13r[2],_13t=E(_13m),_13u=E(_13r[1]),_13v=_13u[2],_13w=E(_13t[1]),_13x=E(_13u[1]);if(_13w>=_13x){if(_13w!=_13x){return [0,_13i,_11,_13k];}else{var _13y=E(_13v);if(E(_13t[2])<_13y){var _13z=B(_12y(_13c>>1,_13x,_13y,_13s,_13q)),_13A=_13z[1],_13B=new T(function(){return B(_7T(_13t,_13n,_13i,_13A));});return [0,_13B,_13z[2],_13z[3]];}else{return [0,_13i,_11,_13k];}}}else{var _13C=B(_134(_13c>>1,_13x,_13v,_13s,_13q)),_13D=_13C[1],_13E=new T(function(){return B(_7T(_13t,_13n,_13i,_13D));});return [0,_13E,_13C[2],_13C[3]];}}}}},_13F=function(_13G,_13H){while(1){var _13I=E(_13H);if(!_13I[0]){return E(_13G);}else{var _13J=E(_13I[1]),_13K=E(_13J[1]),_13L=B(_VQ(_13K[1],_13K[2],_13J[2],_13G));_13H=_13I[2];_13G=_13L;continue;}}},_13M=function(_13N,_13O,_13P,_13Q,_13R){return new F(function(){return _13F(B(_VQ(_13O,_13P,_13Q,_13N)),_13R);});},_13S=function(_13T,_13U,_13V){var _13W=E(_13U),_13X=E(_13W[1]);return new F(function(){return _13F(B(_VQ(_13X[1],_13X[2],_13W[2],_13T)),_13V);});},_13Y=function(_13Z,_140,_141){var _142=E(_141);if(!_142[0]){return E(_140);}else{var _143=E(_142[1]),_144=_143[1],_145=_143[2],_146=E(_142[2]);if(!_146[0]){return new F(function(){return _6o(_144,_145,_140);});}else{var _147=_146[2],_148=E(_146[1]),_149=_148[2],_14a=E(_144),_14b=_14a[2],_14c=E(_148[1]),_14d=_14c[2],_14e=E(_14a[1]),_14f=E(_14c[1]),_14g=function(_14h){var _14i=B(_134(_13Z,_14f,_14d,_149,_147)),_14j=_14i[1],_14k=E(_14i[3]);if(!_14k[0]){return new F(function(){return _13Y(_13Z<<1,B(_7T(_14a,_145,_140,_14j)),_14i[2]);});}else{return new F(function(){return _13S(B(_7T(_14a,_145,_140,_14j)),_14k[1],_14k[2]);});}};if(_14e>=_14f){if(_14e!=_14f){return new F(function(){return _13M(_140,_14e,_14b,_145,_146);});}else{var _14l=E(_14b);if(_14l<E(_14d)){return new F(function(){return _14g(_);});}else{return new F(function(){return _13M(_140,_14e,_14l,_145,_146);});}}}else{return new F(function(){return _14g(_);});}}}},_14m=function(_14n,_14o,_14p,_14q,_14r,_14s){var _14t=E(_14s);if(!_14t[0]){return new F(function(){return _6o([0,_14p,_14q],_14r,_14o);});}else{var _14u=_14t[2],_14v=E(_14t[1]),_14w=_14v[2],_14x=E(_14v[1]),_14y=_14x[2],_14z=E(_14x[1]),_14A=function(_14B){var _14C=B(_134(_14n,_14z,_14y,_14w,_14u)),_14D=_14C[1],_14E=E(_14C[3]);if(!_14E[0]){return new F(function(){return _13Y(_14n<<1,B(_7T([0,_14p,_14q],_14r,_14o,_14D)),_14C[2]);});}else{return new F(function(){return _13S(B(_7T([0,_14p,_14q],_14r,_14o,_14D)),_14E[1],_14E[2]);});}};if(_14p>=_14z){if(_14p!=_14z){return new F(function(){return _13M(_14o,_14p,_14q,_14r,_14t);});}else{if(_14q<E(_14y)){return new F(function(){return _14A(_);});}else{return new F(function(){return _13M(_14o,_14p,_14q,_14r,_14t);});}}}else{return new F(function(){return _14A(_);});}}},_14F=function(_14G,_14H,_14I,_14J,_14K,_14L){var _14M=E(_14L);if(!_14M[0]){return new F(function(){return _6o([0,_14I,_14J],_14K,_14H);});}else{var _14N=_14M[2],_14O=E(_14M[1]),_14P=_14O[2],_14Q=E(_14O[1]),_14R=_14Q[2],_14S=E(_14Q[1]),_14T=function(_14U){var _14V=B(_134(_14G,_14S,_14R,_14P,_14N)),_14W=_14V[1],_14X=E(_14V[3]);if(!_14X[0]){return new F(function(){return _13Y(_14G<<1,B(_7T([0,_14I,_14J],_14K,_14H,_14W)),_14V[2]);});}else{return new F(function(){return _13S(B(_7T([0,_14I,_14J],_14K,_14H,_14W)),_14X[1],_14X[2]);});}};if(_14I>=_14S){if(_14I!=_14S){return new F(function(){return _13M(_14H,_14I,_14J,_14K,_14M);});}else{var _14Y=E(_14J);if(_14Y<E(_14R)){return new F(function(){return _14T(_);});}else{return new F(function(){return _13M(_14H,_14I,_14Y,_14K,_14M);});}}}else{return new F(function(){return _14T(_);});}}},_14Z=function(_150){var _151=E(_150);if(!_151[0]){return [1];}else{var _152=E(_151[1]),_153=_152[1],_154=_152[2],_155=E(_151[2]);if(!_155[0]){return [0,1,E(_153),_154,E(_5z),E(_5z)];}else{var _156=_155[2],_157=E(_155[1]),_158=_157[2],_159=E(_153),_15a=E(_157[1]),_15b=_15a[2],_15c=E(_159[1]),_15d=E(_15a[1]);if(_15c>=_15d){if(_15c!=_15d){return new F(function(){return _13M([0,1,E(_159),_154,E(_5z),E(_5z)],_15d,_15b,_158,_156);});}else{var _15e=E(_15b);if(E(_159[2])<_15e){return new F(function(){return _14m(1,[0,1,E(_159),_154,E(_5z),E(_5z)],_15d,_15e,_158,_156);});}else{return new F(function(){return _13M([0,1,E(_159),_154,E(_5z),E(_5z)],_15d,_15e,_158,_156);});}}}else{return new F(function(){return _14F(1,[0,1,E(_159),_154,E(_5z),E(_5z)],_15d,_15b,_158,_156);});}}}},_15f=new T(function(){return B(_zj(0,34));}),_15g=function(_15h){var _15i=_15h,_15j=new T(function(){var _15k=E(_15h);if(_15k==44){return [0];}else{return B(_15g(_15k+1|0));}}),_15l=function(_15m){var _15n=E(_15m);if(!_15n[0]){return E(_15j);}else{var _15o=_15n[2],_15p=new T(function(){return B(_15l(_15o));});return [1,[0,_15i,_15n[1]],_15p];}};return new F(function(){return _15l(_15f);});},_15q=new T(function(){return B(_15g(0));}),_15r=32,_15s=new T(function(){return [1,_15r,_15s];}),_15t=new T(function(){return B(_Ou(_15q,_15s));}),_15u=new T(function(){return B(_14Z(_15t));}),_15v=35,_15w=function(_15x){return E(E(_15x)[1]);},_15y=function(_15z,_15A,_15B){while(1){var _15C=E(_15B);if(!_15C[0]){return false;}else{if(!B(A(_15w,[_15z,_15A,_15C[1]]))){_15B=_15C[2];continue;}else{return true;}}}},_15D=function(_15E){return E(E(_15E)[1]);},_15F=function(_15G){var _15H=E(_15G);if(!_15H[0]){return [0];}else{var _15I=_15H[2],_15J=new T(function(){return B(_15F(_15I));},1);return new F(function(){return _v(_15H[1],_15J);});}},_15K=function(_15L){return new F(function(){return _oN("Dungeon.hs:(127,5)-(128,21)|function tup");});},_15M=new T(function(){return B(_15K(_));}),_15N=function(_15O){var _15P=E(_15O);if(!_15P[0]){return E(_15M);}else{var _15Q=_15P[1],_15R=E(_15P[2]);return (_15R[0]==0)?[0,_15Q,_15Q]:(E(_15R[2])[0]==0)?[0,_15Q,_15R[1]]:E(_15M);}},_15S=function(_15T,_15U){return new F(function(){return _59(E(E(_15T)[2]),E(E(_15U)[2]));});},_15V=function(_15W){var _15X=E(_15W);if(!_15X[0]){return [0];}else{var _15Y=_15X[2],_15Z=new T(function(){return B(_15V(_15Y));}),_160=function(_161){var _162=E(_161);if(!_162[0]){return E(_15Z);}else{var _163=_162[1],_164=_162[2],_165=new T(function(){return B(_160(_164));}),_166=new T(function(){return B(_15N(_163));});return [1,_166,_165];}};return new F(function(){return _160(B(_VH(2,B(_h5(_15S,_15X[1])))));});}},_167=function(_168,_169){var _16a=E(_169);if(!_16a[0]){return [0];}else{var _16b=_16a[1],_16c=_16a[2],_16d=new T(function(){var _16e=new T(function(){return B(A(_168,[_16b]));}),_16f=B(_on(_16e,_16c));return [0,_16f[1],_16f[2]];}),_16g=new T(function(){return B(_167(_168,E(_16d)[2]));}),_16h=new T(function(){return E(E(_16d)[1]);});return [1,[1,_16b,_16h],_16g];}},_16i=function(_16j,_16k){return E(E(_16j)[1])==E(E(_16k)[1]);},_16l=function(_16m,_16n){return new F(function(){return _59(E(E(_16m)[1]),E(E(_16n)[1]));});},_16o=45,_16p=function(_16q,_16r){return E(E(_16q)[2])==E(E(_16r)[2]);},_16s=function(_16t,_16u,_16v,_16w){var _16x=E(_16w);if(!_16x[0]){var _16y=_16x[3],_16z=_16x[4],_16A=_16x[5],_16B=E(_16x[2]),_16C=E(_16B[1]);if(_16t>=_16C){if(_16t!=_16C){return new F(function(){return _5E(_16B,_16y,_16z,B(_16s(_16t,_16u,_16v,_16A)));});}else{var _16D=E(_16B[2]);if(_16u>=_16D){if(_16u!=_16D){return new F(function(){return _5E(_16B,_16y,_16z,B(_16s(_16t,_16u,_16v,_16A)));});}else{return [0,_16x[1],[0,_16t,_16u],_16v,E(_16z),E(_16A)];}}else{return new F(function(){return _6x(_16B,_16y,B(_16s(_16t,_16u,_16v,_16z)),_16A);});}}}else{return new F(function(){return _6x(_16B,_16y,B(_16s(_16t,_16u,_16v,_16z)),_16A);});}}else{return [0,1,[0,_16t,_16u],_16v,E(_5z),E(_5z)];}},_16E=function(_16F,_16G,_16H,_16I){var _16J=E(_16I);if(!_16J[0]){var _16K=_16J[3],_16L=_16J[4],_16M=_16J[5],_16N=E(_16J[2]),_16O=E(_16N[1]);if(_16F>=_16O){if(_16F!=_16O){return new F(function(){return _5E(_16N,_16K,_16L,B(_16E(_16F,_16G,_16H,_16M)));});}else{var _16P=E(_16G),_16Q=E(_16N[2]);if(_16P>=_16Q){if(_16P!=_16Q){return new F(function(){return _5E(_16N,_16K,_16L,B(_16s(_16F,_16P,_16H,_16M)));});}else{return [0,_16J[1],[0,_16F,_16P],_16H,E(_16L),E(_16M)];}}else{return new F(function(){return _6x(_16N,_16K,B(_16s(_16F,_16P,_16H,_16L)),_16M);});}}}else{return new F(function(){return _6x(_16N,_16K,B(_16E(_16F,_16G,_16H,_16L)),_16M);});}}else{return [0,1,[0,_16F,_16G],_16H,E(_5z),E(_5z)];}},_16R=function(_16S,_16T,_16U){var _16V=new T(function(){return [1,_16S,_16V];}),_16W=function(_16X){var _16Y=E(_16X);if(!_16Y[0]){return E(_16U);}else{var _16Z=E(_16Y[1]),_170=E(_16Z[1]),_171=E(_16Z[2]),_172=E(_170[1]),_173=E(_171[1]),_174=B(_16W(_16Y[2]));if(_172<=_173){var _175=B(_zj(E(_170[2]),E(_171[2]))),_176=function(_177,_178){var _179=new T(function(){return _177==_173;}),_17a=function(_17b,_17c){var _17d=E(_17b);if(!_17d[0]){if(!E(_179)){return new F(function(){return _176(_177+1|0,_17c);});}else{return E(_174);}}else{var _17e=E(_17c);if(!_17e[0]){return E(_174);}else{return new F(function(){return _16E(_177,_17d[1],_17e[1],B(_17a(_17d[2],_17e[2])));});}}};return new F(function(){return _17a(_175,_178);});};return new F(function(){return _176(_172,_16V);});}else{return E(_174);}}};return new F(function(){return _16W(_16T);});},_17f=function(_17g){return E(E(_17g)[2]);},_17h=function(_){var _17i=B(_Yd(0,_)),_17j=B(_Yn(_17i,_)),_17k=_17j,_17l=B(_102(_17i,_17k,_)),_17m=_17l,_17n=B(_10F(_17i,_17k,_)),_17o=_17n,_17p=B(_11i(_17i,_17k,_)),_17q=_17p,_17r=B(_11V(_17i,_17k,_)),_17s=_17r;return new T(function(){var _17t=new T(function(){var _17u=new T(function(){var _17v=new T(function(){return B(_15F(_17s));}),_17w=function(_17x){var _17y=E(_17x);if(!_17y[0]){return E(_17v);}else{var _17z=_17y[2],_17A=new T(function(){return B(_17w(_17z));},1);return new F(function(){return _v(_17y[1],_17A);});}};return B(_17w(_17q));}),_17B=function(_17C){var _17D=E(_17C);if(!_17D[0]){return E(_17u);}else{var _17E=_17D[2],_17F=new T(function(){return B(_17B(_17E));},1);return new F(function(){return _v(_17D[1],_17F);});}};return B(_17B(_17o));}),_17G=function(_17H){var _17I=E(_17H);if(!_17I[0]){return E(_17t);}else{var _17J=_17I[2],_17K=new T(function(){return B(_17G(_17J));},1);return new F(function(){return _v(_17I[1],_17K);});}},_17L=B(_17G(_17m)),_17M=B(_zD(_15D,_17L)),_17N=new T(function(){return B(_zD(_17f,_17L));}),_17O=new T(function(){var _17P=function(_17Q){while(1){var _17R=(function(_17S){var _17T=E(_17S);if(!_17T[0]){return [0];}else{var _17U=_17T[2],_17V=E(_17T[1]),_17W=E(_17V[1]),_17X=E(_17V[2]);if(E(_17W[2])!=E(_17X[2])){_17Q=_17U;return null;}else{var _17Y=new T(function(){return B(_17P(_17U));}),_17Z=new T(function(){if(!B(_15y(_qC,_17W,_17N))){return E(_17X);}else{return E(_17W);}});return [1,_17Z,_17Y];}}})(_17Q);if(_17R!=null){return _17R;}}};return B(_15V(B(_167(_16i,B(_h5(_16l,B(_17P(_17M))))))));}),_180=function(_181){var _182=E(_181);if(!_182[0]){return E(_17O);}else{var _183=_182[2],_184=new T(function(){return B(_180(_183));}),_185=function(_186){var _187=E(_186);if(!_187[0]){return E(_184);}else{var _188=_187[1],_189=_187[2],_18a=new T(function(){return B(_185(_189));}),_18b=new T(function(){return B(_15N(_188));});return [1,_18b,_18a];}};return new F(function(){return _185(B(_VH(2,B(_h5(_16l,_182[1])))));});}},_18c=function(_18d){while(1){var _18e=(function(_18f){var _18g=E(_18f);if(!_18g[0]){return [0];}else{var _18h=_18g[2],_18i=E(_18g[1]),_18j=E(_18i[1]),_18k=E(_18i[2]);if(E(_18j[1])!=E(_18k[1])){_18d=_18h;return null;}else{var _18l=new T(function(){return B(_18c(_18h));}),_18m=new T(function(){if(!B(_15y(_qC,_18j,_17N))){return E(_18k);}else{return E(_18j);}});return [1,_18m,_18l];}}})(_18d);if(_18e!=null){return _18e;}}},_18n=B(_16R(_15v,_17k,B(_16R(_16o,_17M,B(_16R(_16o,B(_180(B(_167(_16p,B(_h5(_15S,B(_18c(_17M)))))))),_15u)))))),_18o=function(_18p){var _18q=E(_18p);if(!_18q[0]){return E(_18n);}else{var _18r=_18q[2],_18s=E(_18q[1]),_18t=E(_18s[1]),_18u=E(_18s[2]);if(!B(_15y(_qC,_18t,_17N))){return new F(function(){return _VQ(_18t[1],_18t[2],_15v,B(_18o(_18r)));});}else{return new F(function(){return _VQ(_18u[1],_18u[2],_15v,B(_18o(_18r)));});}}};return B(_18o(_17M));});},_18v=new T(function(){return B(unCStr("    <div class=\"progress\">"));}),_18w=new T(function(){return B(unCStr("  <div class=\"col-md-8\">"));}),_18x=new T(function(){return B(unCStr("<div class=\"row\">"));}),_18y=function(_18z){var _18A=E(_18z);if(!_18A[0]){return [0];}else{var _18B=_18A[2],_18C=new T(function(){return B(_18y(_18B));},1);return new F(function(){return _v(_18A[1],_18C);});}},_18D=function(_18E,_18F){var _18G=new T(function(){return B(_18y(_18F));},1);return new F(function(){return _v(_18E,_18G);});},_18H=new T(function(){return B(unCStr("</div>"));}),_18I=[1,_18H,_11],_18J=new T(function(){return B(unCStr("  </div>"));}),_18K=[1,_18J,_18I],_18L=new T(function(){return B(unCStr("    </div>"));}),_18M=new T(function(){return B(_18D(_18L,_18K));}),_18N=new T(function(){return B(unAppCStr("%;\"></div>",_18M));}),_18O=function(_18P){var _18Q=E(_18P);if(!_18Q[0]){return [0];}else{var _18R=_18Q[2],_18S=new T(function(){return B(_18O(_18R));},1);return new F(function(){return _v(_18Q[1],_18S);});}},_18T=function(_18U,_18V){var _18W=new T(function(){return B(_18O(_18V));},1);return new F(function(){return _v(_18U,_18W);});},_18X=new T(function(){return B(unCStr("      \u7279\u6b8a\u9663\u55b6\u30fb\u30c7\u30c3\u30ad\u62e1\u5f35\u30fb\u738b\u306e\u529b"));}),_18Y=[1,_18H,_18I],_18Z=[1,_18H,_18Y],_190=[1,_18J,_18Z],_191=new T(function(){return B(unCStr("    <div id=\"join-party-btn\"></div>"));}),_192=[1,_191,_190],_193=new T(function(){return B(unCStr("    </p>"));}),_194=[1,_193,_192],_195=[1,_18X,_194],_196=new T(function(){return B(unCStr("      <strong>\u56fa\u6709\u30b9\u30ad\u30eb</strong><br>"));}),_197=[1,_196,_195],_198=new T(function(){return B(unCStr("    <p>"));}),_199=new T(function(){return B(_18T(_198,_197));}),_19a=function(_19b,_19c){var _19d=E(_19b);if(!_19d[0]){return E(_199);}else{var _19e=_19d[1],_19f=_19d[2],_19g=E(_19c);if(!_19g[0]){return E(_199);}else{var _19h=_19g[1],_19i=_19g[2],_19j=new T(function(){return B(_19a(_19f,_19i));},1),_19k=new T(function(){var _19l=new T(function(){var _19m=new T(function(){var _19n=new T(function(){var _19o=new T(function(){var _19p=new T(function(){var _19q=new T(function(){return B(_v(B(_H(0,E(_19h),_11)),_18N));});return B(unAppCStr("      <div class=\"progress-bar\" role=\"progressbar\" style=\"width: ",_19q));},1);return B(_v(_18v,_19p));},1);return B(_v(_18w,_19o));});return B(unAppCStr("</div>",_19n));},1);return B(_v(_19e,_19m));});return B(unAppCStr("  <div class=\"col-md-3\">",_19l));},1);return new F(function(){return _v(B(_v(_18x,_19k)),_19j);});}}},_19r=function(_19s,_19t,_19u,_19v){var _19w=new T(function(){return B(_19a(_19t,_19v));},1),_19x=new T(function(){var _19y=new T(function(){var _19z=new T(function(){var _19A=new T(function(){var _19B=new T(function(){var _19C=new T(function(){var _19D=new T(function(){return B(_v(B(_H(0,E(_19u),_11)),_18N));});return B(unAppCStr("      <div class=\"progress-bar\" role=\"progressbar\" style=\"width: ",_19D));},1);return B(_v(_18v,_19C));},1);return B(_v(_18w,_19B));});return B(unAppCStr("</div>",_19A));},1);return B(_v(_19s,_19z));});return B(unAppCStr("  <div class=\"col-md-3\">",_19y));},1);return new F(function(){return _v(B(_v(_18x,_19x)),_19w);});},_19E=new T(function(){return B(unCStr("MP"));}),_19F=[1,_19E,_11],_19G=new T(function(){return B(unCStr("HP"));}),_19H=[1,_19G,_19F],_19I=new T(function(){return B(unCStr("LV"));}),_19J=[1,_19I,_19H],_19K=new T(function(){return B(unCStr("LUC"));}),_19L=[1,_19K,_19J],_19M=new T(function(){return B(unCStr("AGI"));}),_19N=[1,_19M,_19L],_19O=new T(function(){return B(unCStr("VIT"));}),_19P=[1,_19O,_19N],_19Q=new T(function(){return B(unCStr("TEC"));}),_19R=[1,_19Q,_19P],_19S=new T(function(){return B(unCStr("INT"));}),_19T=[1,_19S,_19R],_19U=new T(function(){return B(unCStr("STR"));}),_19V=new T(function(){return B(unCStr("  <div class=\"panel-body\">"));}),_19W=[1,_19V,_11],_19X=[1,_18J,_19W],_19Y=new T(function(){return B(unCStr("    </h3>"));}),_19Z=new T(function(){return B(unCStr("    <h3 class=\"panel-title\">"));}),_1a0=new T(function(){return B(unCStr("  <div class=\"panel-heading\">"));}),_1a1=new T(function(){return B(unCStr("<div class=\"panel panel-default\">"));}),_1a2=function(_1a3){var _1a4=new T(function(){var _1a5=E(_1a3),_1a6=_1a5[1],_1a7=_1a5[2],_1a8=_1a5[3],_1a9=_1a5[4],_1aa=_1a5[5],_1ab=_1a5[6],_1ac=_1a5[7],_1ad=_1a5[8],_1ae=_1a5[9],_1af=_1a5[11],_1ag=new T(function(){var _1ah=new T(function(){var _1ai=new T(function(){var _1aj=new T(function(){var _1ak=new T(function(){var _1al=new T(function(){var _1am=new T(function(){var _1an=new T(function(){var _1ao=new T(function(){return B(_19r(_19U,_19T,_1a7,[1,_1a8,[1,_1a9,[1,_1aa,[1,_1ab,[1,_1ac,[1,_1ad,[1,_1ae,[1,_1af,_11]]]]]]]]));}),_1ap=function(_1aq){var _1ar=E(_1aq);if(!_1ar[0]){return E(_1ao);}else{var _1as=_1ar[2],_1at=new T(function(){return B(_1ap(_1as));},1);return new F(function(){return _v(_1ar[1],_1at);});}},_1au=function(_1av,_1aw){var _1ax=new T(function(){return B(_1ap(_1aw));},1);return new F(function(){return _v(_1av,_1ax);});};return B(_1au(_19Y,_19X));});return B(unAppCStr("(<a data-toggle=\"modal\" data-target=\"#myModal\"> S </a> )",_1an));},1);return B(_v(_1a6,_1am));});return B(unAppCStr("      ",_1al));},1);return B(_v(_19Z,_1ak));},1);return B(_v(_1a0,_1aj));},1);return B(_v(_1a1,_1ai));});return B(unAppCStr("\">",_1ah));},1);return B(_v(_1a6,_1ag));});return new F(function(){return unAppCStr("<div class=\"col-md-4 career\" id=\"character-detail-",_1a4);});},_1ay=function(_1az,_1aA){return new F(function(){return _bF(_1az,E(_1aA));});},_1aB=new T(function(){return B(unCStr("Map.!: given key is not an element in the map"));}),_1aC=new T(function(){return B(err(_1aB));}),_1aD=function(_1aE,_1aF,_1aG){while(1){var _1aH=E(_1aG);if(!_1aH[0]){var _1aI=_1aH[4],_1aJ=_1aH[5],_1aK=E(_1aH[2]),_1aL=E(_1aK[1]);if(_1aE>=_1aL){if(_1aE!=_1aL){_1aG=_1aJ;continue;}else{var _1aM=E(_1aK[2]);if(_1aF>=_1aM){if(_1aF!=_1aM){_1aG=_1aJ;continue;}else{return E(_1aH[3]);}}else{_1aG=_1aI;continue;}}}else{_1aG=_1aI;continue;}}else{return E(_1aC);}}},_1aN=function(_1aO,_1aP,_1aQ){while(1){var _1aR=E(_1aQ);if(!_1aR[0]){var _1aS=_1aR[4],_1aT=_1aR[5],_1aU=E(_1aR[2]),_1aV=E(_1aU[1]);if(_1aO>=_1aV){if(_1aO!=_1aV){_1aQ=_1aT;continue;}else{var _1aW=E(_1aP),_1aX=E(_1aU[2]);if(_1aW>=_1aX){if(_1aW!=_1aX){return new F(function(){return _1aD(_1aO,_1aW,_1aT);});}else{return E(_1aR[3]);}}else{return new F(function(){return _1aD(_1aO,_1aW,_1aS);});}}}else{_1aQ=_1aS;continue;}}else{return E(_1aC);}}},_1aY=new T(function(){return B(_zj(0,20));}),_1aZ=function(_1b0,_){var _1b1=E(_WD)(),_1b2=_1b1;return new T(function(){var _1b3=function(_1b4){var _1b5=E(_1b4);if(!_1b5[0]){return [0];}else{var _1b6=_1b5[2],_1b7=new T(function(){return B(_1b3(_1b6));}),_1b8=E(_1aY);if(!_1b8[0]){return E(_1b7);}else{var _1b9=_1b8[1],_1ba=_1b8[2],_1bb=E(_1b5[1]),_1bc=_1bb;if(E(B(_1aN(_1bc,_1b9,_1b0)))==35){var _1bd=new T(function(){var _1be=function(_1bf){while(1){var _1bg=(function(_1bh){var _1bi=E(_1bh);if(!_1bi[0]){return E(_1b7);}else{var _1bj=_1bi[1],_1bk=_1bi[2];if(E(B(_1aN(_1bc,_1bj,_1b0)))==35){var _1bl=new T(function(){return B(_1be(_1bk));});return [1,[0,_1bb,_1bj],_1bl];}else{_1bf=_1bk;return null;}}})(_1bf);if(_1bg!=null){return _1bg;}}};return B(_1be(_1ba));});return [1,[0,_1bb,_1b9],_1bd];}else{var _1bm=function(_1bn){while(1){var _1bo=(function(_1bp){var _1bq=E(_1bp);if(!_1bq[0]){return E(_1b7);}else{var _1br=_1bq[1],_1bs=_1bq[2];if(E(B(_1aN(_1bc,_1br,_1b0)))==35){var _1bt=new T(function(){return B(_1bm(_1bs));});return [1,[0,_1bb,_1br],_1bt];}else{_1bn=_1bs;return null;}}})(_1bn);if(_1bo!=null){return _1bo;}}};return new F(function(){return _1bm(_1ba);});}}}},_1bu=B(_1b3(_1aY));return B(_1ay(_1bu,B(_Wn(0,B(_Ol(_1bu,0))-1|0,_1b2))[1]));});},_1bv=new T(function(){return B(unCStr("\u30c7\u30d3\u30eb\u30a8\u30f3\u30da\u30e9\u30fc"));}),_1bw=0,_1bx=[1,_1bw,_11],_1by=[1,_1bw,_1bx],_1bz=[1,_1bw,_1by],_1bA=new T(function(){return B(_Ou(_Ot,_1bz));}),_1bB=new T(function(){return B(_P4(_Os,_1bA));}),_1bC=new T(function(){return B(_Ol(_1bz,0));}),_1bD=[0,_Pc,_1bC,_1bB],_1bE=5000,_1bF=[0,_1bv,_Pq,_Pq,_Pq,_Pp,_Pr,_Pe,_Pf,_1bE,_1bE,_Pr,_Pr,_1bD],_1bG=[1,_1bF,_11],_1bH=[0,_Qe,_PH,_PG,_Pr,_PI,_Pe,_Pp,_Pf,_Pg,_Pg,_Pq,_Pq,_Pd],_1bI=[1,_1bH,_11],_1bJ=[1,_Q9,_1bI],_1bK=[1,_Qd,_1bJ],_1bL=100,_1bM=new T(function(){return B(unCStr("\u30d7\u30ea\u30f3\u30bb\u30b9"));}),_1bN=[1,_1bw,_11],_1bO=[1,_1bw,_1bN],_1bP=[1,_1bw,_1bO],_1bQ=new T(function(){return B(_Ou(_Ot,_1bP));}),_1bR=new T(function(){return B(_P4(_Os,_1bQ));}),_1bS=new T(function(){return B(_Ol(_1bP,0));}),_1bT=[0,_Pc,_1bS,_1bR],_1bU=[0,_1bM,_1bT],_1bV=[1,_1bU,_11],_1bW=new T(function(){return B(_9q(_1bV));}),_1bX=[0,_1bL,_1bW],_1bY=[1,_1bX,_11],_1bZ=new T(function(){return B(_P4(_Os,_1bY));}),_1c0=[0,_1bK,_1bG,_za,_1bZ],_1c1=46,_1c2=new T(function(){return [1,_1c1,_1c2];}),_1c3=new T(function(){return B(_Ou(_15q,_1c2));}),_1c4=new T(function(){return B(_14Z(_1c3));}),_1c5=function(_1c6){var _1c7=new T(function(){var _1c8=E(_1c6);if(_1c8==255){return [0];}else{var _1c9=B(_1c5(_1c8+1|0));return [1,_1c9[1],_1c9[2]];}});return [0,[0,_1c6,_Ve],_1c7];},_1ca=new T(function(){var _1cb=B(_1c5(0));return B(_P4(_Os,[1,_1cb[1],_1cb[2]]));}),_1cc=function(_1cd,_1ce){var _1cf=E(_1cd);if(!_1cf[0]){return [0];}else{var _1cg=_1cf[1],_1ch=_1cf[2],_1ci=E(_1ce);if(!_1ci[0]){return [0];}else{var _1cj=_1ci[2],_1ck=new T(function(){return B(_1cc(_1ch,_1cj));}),_1cl=new T(function(){return E(E(_1cg)[1]);});return [1,[0,_1cl,_1ci[1]],_1ck];}}},_1cm=(function(e,c) {return e.classList.contains(c);}),_1cn=function(_1co,_1cp){while(1){var _1cq=(function(_1cr,_1cs){var _1ct=E(_1cs);switch(_1ct[0]){case 0:var _1cu=_1ct[4],_1cv=new T(function(){return B(_1cn(_1cr,_1cu));});_1co=_1cv;_1cp=_1ct[3];return null;case 1:return [1,_1ct[1],_1cr];default:return E(_1cr);}})(_1co,_1cp);if(_1cq!=null){return _1cq;}}},_1cw=function(_1cx){var _1cy=E(_1cx);if(!_1cy[0]){var _1cz=_1cy[3],_1cA=_1cy[4];if(_1cy[2]>=0){var _1cB=new T(function(){return B(_1cn(_11,_1cA));});return new F(function(){return _1cn(_1cB,_1cz);});}else{var _1cC=new T(function(){return B(_1cn(_11,_1cz));});return new F(function(){return _1cn(_1cC,_1cA);});}}else{return new F(function(){return _1cn(_11,_1cy);});}},_1cD=new T(function(){return B(unCStr("active"));}),_1cE=[1,_1bH,_Qa],_1cF=function(_1cG){return E(E(_1cG)[7]);},_1cH=new T(function(){return B(unCStr("maximum"));}),_1cI=new T(function(){return B(_a5(_1cH));}),_1cJ=function(_1cK,_1cL){var _1cM=E(_1cL);if(!_1cM[0]){return E(_1cI);}else{var _1cN=new T(function(){return B(_1cF(_1cK));}),_1cO=_1cM[2],_1cP=_1cM[1];while(1){var _1cQ=E(_1cO);if(!_1cQ[0]){return E(_1cP);}else{_1cO=_1cQ[2];var _1cR=B(A(_1cN,[E(_1cP),_1cQ[1]]));_1cP=_1cR;continue;}}}},_1cS=function(_){return _eF;},_1cT="tactic-detail",_1cU="tactic-list-tbody",_1cV=function() { $('.selectpicker').selectpicker(); },_1cW=new T(function(){return B(unCStr("head"));}),_1cX=new T(function(){return B(_a5(_1cW));}),_1cY=function(_1cZ,_1d0){while(1){var _1d1=E(_1d0);if(!_1d1[0]){_1cZ=_1d1[3];_1d0=_1d1[4];continue;}else{return E(_1cZ);}}},_1d2=function(_1d3,_1d4){while(1){var _1d5=(function(_1d6,_1d7){var _1d8=E(_1d7);if(!_1d8[0]){var _1d9=_1d8[5],_1da=new T(function(){return B(_1d2(_1d6,_1d9));});_1d3=[1,_1d8[2],_1da];_1d4=_1d8[4];return null;}else{return E(_1d6);}})(_1d3,_1d4);if(_1d5!=null){return _1d5;}}},_1db=new T(function(){return B(unCStr("</tr>"));}),_1dc=new T(function(){return B(unCStr("\">\u7de8\u96c6</button></td>"));}),_1dd=new T(function(){return B(_v(_1dc,_1db));}),_1de=new T(function(){return B(unCStr("\u30fb"));}),_1df=new T(function(){return B(unCStr("<tr>"));}),_1dg=function(_1dh,_1di){while(1){var _1dj=(function(_1dk,_1dl){var _1dm=E(_1dl);switch(_1dm[0]){case 0:var _1dn=_1dm[4],_1do=new T(function(){return B(_1dg(_1dk,_1dn));},1);_1dh=_1do;_1di=_1dm[3];return null;case 1:var _1dp=_1dm[1],_1dq=_1dm[2],_1dr=new T(function(){var _1ds=new T(function(){var _1dt=new T(function(){var _1du=new T(function(){var _1dv=new T(function(){var _1dw=new T(function(){var _1dx=new T(function(){var _1dy=new T(function(){return B(_v(B(_H(0,_1dp,_11)),_1dd));});return B(unAppCStr("</td>  <td><button type=\"button\" class=\"btn btn-default btn-sm\" id=\"edit-tactic-",_1dy));},1);return B(_v(B(_H(0,E(B(_1cY(_1cX,_1dq))[2]),_11)),_1dx));});return B(unAppCStr("</td>  <td>",_1dw));}),_1dz=B(_1d2(_11,_1dq));if(!_1dz[0]){return E(_1dv);}else{var _1dA=_1dz[2],_1dB=function(_1dC){var _1dD=E(_1dC);if(!_1dD[0]){return E(_1dv);}else{var _1dE=_1dD[2],_1dF=new T(function(){return B(_1dB(_1dE));},1);return new F(function(){return _v(_1dD[1],_1dF);});}},_1dG=function(_1dH,_1dI){var _1dJ=new T(function(){return B(_1dB(_1dI));},1);return new F(function(){return _v(_1dH,_1dJ);});},_1dK=new T(function(){return B(_zL(_1de,_1dA));});return B(_1dG(_1dz[1],_1dK));}});return B(unAppCStr("</td>  <td>",_1du));},1);return B(_v(B(_H(0,_1dp,_11)),_1dt));});return B(unAppCStr("  <td>",_1ds));},1);return new F(function(){return _v(B(_v(_1df,_1dr)),_1dk);});break;default:return E(_1dk);}})(_1dh,_1di);if(_1dj!=null){return _1dj;}}},_1dL=function(_1dM){var _1dN=E(_1dM);if(!_1dN[0]){var _1dO=_1dN[3],_1dP=_1dN[4];if(_1dN[2]>=0){var _1dQ=new T(function(){return B(_1dg(_11,_1dP));},1);return new F(function(){return _1dg(_1dQ,_1dO);});}else{var _1dR=new T(function(){return B(_1dg(_11,_1dO));},1);return new F(function(){return _1dg(_1dR,_1dP);});}}else{return new F(function(){return _1dg(_11,_1dN);});}},_1dS=new T(function(){return B(unCStr("</th>"));}),_1dT=function(_1dU,_1dV){while(1){var _1dW=(function(_1dX,_1dY){var _1dZ=E(_1dY);if(!_1dZ[0]){var _1e0=_1dZ[2],_1e1=_1dZ[5],_1e2=new T(function(){var _1e3=new T(function(){return B(_1dT(_1dX,_1e1));},1),_1e4=new T(function(){return B(_v(_1e0,_1dS));});return B(_v(B(unAppCStr("<th>",_1e4)),_1e3));},1);_1dU=_1e2;_1dV=_1dZ[4];return null;}else{return E(_1dX);}})(_1dU,_1dV);if(_1dW!=null){return _1dW;}}},_1e5=function(_1e6){while(1){var _1e7=E(_1e6);if(!_1e7[0]){_1e6=[1,I_fromInt(_1e7[1])];continue;}else{return new F(function(){return I_toString(_1e7[1]);});}}},_1e8=function(_1e9,_1ea){return new F(function(){return _v(fromJSStr(B(_1e5(_1e9))),_1ea);});},_1eb=function(_1ec,_1ed){var _1ee=E(_1ec);if(!_1ee[0]){var _1ef=_1ee[1],_1eg=E(_1ed);return (_1eg[0]==0)?_1ef<_1eg[1]:I_compareInt(_1eg[1],_1ef)>0;}else{var _1eh=_1ee[1],_1ei=E(_1ed);return (_1ei[0]==0)?I_compareInt(_1eh,_1ei[1])<0:I_compare(_1eh,_1ei[1])<0;}},_1ej=[0,0],_1ek=function(_1el,_1em,_1en){if(_1el<=6){return new F(function(){return _1e8(_1em,_1en);});}else{if(!B(_1eb(_1em,_1ej))){return new F(function(){return _1e8(_1em,_1en);});}else{var _1eo=new T(function(){return B(_v(fromJSStr(B(_1e5(_1em))),[1,_F,_1en]));});return [1,_G,_1eo];}}},_1ep=function(_1eq){var _1er=E(_1eq);if(!_1er[0]){return E(_1db);}else{var _1es=_1er[2],_1et=new T(function(){return B(_1ep(_1es));},1);return new F(function(){return _v(_1er[1],_1et);});}},_1eu=function(_1ev){var _1ew=E(_1ev);if(!_1ew[0]){return [0];}else{var _1ex=_1ew[2],_1ey=new T(function(){return B(_1eu(_1ex));},1);return new F(function(){return _v(_1ew[1],_1ey);});}},_1ez=function(_1eA,_1eB){var _1eC=new T(function(){return B(_1eu(_1eB));},1);return new F(function(){return _v(_1eA,_1eC);});},_1eD=new T(function(){return B(unCStr("    </table>"));}),_1eE=[1,_1eD,_mY],_1eF=new T(function(){return B(unCStr("      </tbody>"));}),_1eG=new T(function(){return B(_1ez(_1eF,_1eE));}),_1eH=function(_1eI,_1eJ){var _1eK=E(_1eI);if(!_1eK[0]){return E(_1eG);}else{var _1eL=_1eK[1],_1eM=_1eK[2],_1eN=E(_1eJ);if(!_1eN[0]){return E(_1eG);}else{var _1eO=_1eN[1],_1eP=_1eN[2],_1eQ=new T(function(){return B(_1eH(_1eM,_1eP));},1),_1eR=new T(function(){var _1eS=new T(function(){var _1eT=new T(function(){return B(_1ep(_1eO));});return B(unAppCStr("</td>",_1eT));},1);return B(_v(B(_1ek(0,_1eL,_11)),_1eS));});return new F(function(){return _v(B(unAppCStr("<tr><td>",_1eR)),_1eQ);});}}},_1eU=function(_1eV,_1eW){while(1){var _1eX=(function(_1eY,_1eZ){var _1f0=E(_1eZ);switch(_1f0[0]){case 0:var _1f1=_1f0[4],_1f2=new T(function(){return B(_1eU(_1eY,_1f1));});_1eV=_1f2;_1eW=_1f0[3];return null;case 1:var _1f3=_1f0[2],_1f4=new T(function(){return B(_9G(_1f3));});return [1,_1f4,_1eY];default:return E(_1eY);}})(_1eV,_1eW);if(_1eX!=null){return _1eX;}}},_1f5=function(_1f6,_1f7){while(1){var _1f8=(function(_1f9,_1fa){var _1fb=E(_1fa);if(!_1fb[0]){var _1fc=_1fb[3],_1fd=_1fb[5],_1fe=new T(function(){return B(_1f5(_1f9,_1fd));}),_1ff=new T(function(){var _1fg=E(E(_1fc)[3]);if(!_1fg[0]){var _1fh=_1fg[3],_1fi=_1fg[4];if(_1fg[2]>=0){var _1fj=new T(function(){return B(_1eU(_11,_1fi));});return B(_1eU(_1fj,_1fh));}else{var _1fk=new T(function(){return B(_1eU(_11,_1fh));});return B(_1eU(_1fk,_1fi));}}else{return B(_1eU(_11,_1fg));}});_1f6=[1,_1ff,_1fe];_1f7=_1fb[4];return null;}else{return E(_1f9);}})(_1f6,_1f7);if(_1f8!=null){return _1f8;}}},_1fl=new T(function(){return B(unCStr("        </tr>"));}),_1fm=new T(function(){return B(unCStr("      </thead>"));}),_1fn=new T(function(){return B(unCStr("      <tbody>"));}),_1fo=[1,_1fn,_11],_1fp=[1,_1fm,_1fo],_1fq=1,_1fr=2,_1fs=[1,_1fr,_11],_1ft=[1,_1fq,_1fs],_1fu=[1,_1bw,_1ft],_1fv=new T(function(){return B(_zD(_9G,_1fu));}),_1fw=new T(function(){return B(unCStr("<select class=\"selectpicker\">"));}),_1fx=new T(function(){return B(unCStr("</option>"));}),_1fy=new T(function(){return B(unCStr("</select>"));}),_1fz=new T(function(){return B(unCStr("</td>"));}),_1fA=new T(function(){return B(_v(_1fy,_1fz));}),_1fB=function(_1fC){var _1fD=new T(function(){var _1fE=new T(function(){var _1fF=function(_1fG){var _1fH=E(_1fG);if(!_1fH[0]){return E(_1fA);}else{var _1fI=_1fH[1],_1fJ=_1fH[2];if(!B(_Od(_1fC,_1fI))){var _1fK=new T(function(){return B(_1fF(_1fJ));},1),_1fL=new T(function(){return B(_v(_1fI,_1fx));});return new F(function(){return _v(B(unAppCStr("<option>",_1fL)),_1fK);});}else{var _1fM=new T(function(){return B(_1fF(_1fJ));},1),_1fN=new T(function(){return B(_v(_1fI,_1fx));});return new F(function(){return _v(B(unAppCStr("<option selected>",_1fN)),_1fM);});}}};return B(_1fF(_1fv));},1);return B(_v(_1fw,_1fE));});return new F(function(){return unAppCStr("<td>",_1fD);});},_1fO=function(_tB){return new F(function(){return _zD(_1fB,_tB);});},_1fP=function(_1fQ,_1fR){while(1){var _1fS=E(_1fQ);if(!_1fS[0]){var _1fT=_1fS[1],_1fU=E(_1fR);if(!_1fU[0]){var _1fV=_1fU[1],_1fW=addC(_1fT,_1fV);if(!E(_1fW[2])){return [0,_1fW[1]];}else{_1fQ=[1,I_fromInt(_1fT)];_1fR=[1,I_fromInt(_1fV)];continue;}}else{_1fQ=[1,I_fromInt(_1fT)];_1fR=_1fU;continue;}}else{var _1fX=E(_1fR);if(!_1fX[0]){_1fQ=_1fS;_1fR=[1,I_fromInt(_1fX[1])];continue;}else{return [1,I_add(_1fS[1],_1fX[1])];}}}},_1fY=function(_1fZ,_1g0){var _1g1=E(_1fZ),_1g2=new T(function(){var _1g3=B(_1fY(B(_1fP(_1g1,_1g0)),_1g0));return [1,_1g3[1],_1g3[2]];});return [0,_1g1,_1g2];},_1g4=[0,1],_1g5=new T(function(){var _1g6=B(_1fY(_1g4,_1g4));return [1,_1g6[1],_1g6[2]];}),_1g7=new T(function(){return B(unCStr("          <th>T</th>"));}),_1g8=[1,_1g7,_11],_1g9=new T(function(){return B(unCStr("        <tr>"));}),_1ga=[1,_1g9,_1g8],_1gb=new T(function(){return B(unCStr("      <thead>"));}),_1gc=[1,_1gb,_1ga],_1gd=new T(function(){return B(unCStr("    <table class=\"table\">"));}),_1ge=[1,_1gd,_1gc],_1gf=new T(function(){return B(unCStr("  <div class=\"panel-body\">"));}),_1gg=new T(function(){return B(unCStr("<div class=\"panel panel-default\">"));}),_1gh=function(_1gi){while(1){var _1gj=(function(_1gk){var _1gl=E(_1gk);if(!_1gl[0]){return [0];}else{var _1gm=_1gl[2],_1gn=E(_1gl[1]);if(!_1gn[0]){_1gi=_1gm;return null;}else{var _1go=new T(function(){return B(_1gh(_1gm));});return [1,_1gn[2],_1go];}}})(_1gi);if(_1gj!=null){return _1gj;}}},_1gp=function(_1gq){while(1){var _1gr=(function(_1gs){var _1gt=E(_1gs);if(!_1gt[0]){return [0];}else{var _1gu=_1gt[2],_1gv=E(_1gt[1]);if(!_1gv[0]){_1gq=_1gu;return null;}else{var _1gw=new T(function(){return B(_1gp(_1gu));});return [1,_1gv[1],_1gw];}}})(_1gq);if(_1gr!=null){return _1gr;}}},_1gx=function(_1gy){while(1){var _1gz=(function(_1gA){var _1gB=E(_1gA);if(!_1gB[0]){return [0];}else{var _1gC=_1gB[2],_1gD=E(_1gB[1]);if(!_1gD[0]){_1gy=_1gC;return null;}else{var _1gE=_1gD[2],_1gF=new T(function(){var _1gG=new T(function(){return B(_1gh(_1gC));});return B(_1gx([1,_1gE,_1gG]));}),_1gH=new T(function(){return B(_1gp(_1gC));});return [1,[1,_1gD[1],_1gH],_1gF];}}})(_1gy);if(_1gz!=null){return _1gz;}}},_1gI=function(_1gJ,_1gK){var _1gL=new T(function(){var _1gM=new T(function(){var _1gN=new T(function(){var _1gO=new T(function(){var _1gP=new T(function(){var _1gQ=new T(function(){var _1gR=new T(function(){var _1gS=new T(function(){return B(_zD(_1fO,B(_1gx(B(_1f5(_11,_1gK))))));},1);return B(_1eH(_1g5,_1gS));}),_1gT=function(_1gU){var _1gV=E(_1gU);if(!_1gV[0]){return E(_1gR);}else{var _1gW=_1gV[2],_1gX=new T(function(){return B(_1gT(_1gW));},1);return new F(function(){return _v(_1gV[1],_1gX);});}},_1gY=function(_1gZ,_1h0){var _1h1=new T(function(){return B(_1gT(_1h0));},1);return new F(function(){return _v(_1gZ,_1h1);});};return B(_1gY(_1fl,_1fp));},1);return B(_1dT(_1gQ,_1gK));}),_1h2=function(_1h3){var _1h4=E(_1h3);if(!_1h4[0]){return E(_1gP);}else{var _1h5=_1h4[2],_1h6=new T(function(){return B(_1h2(_1h5));},1);return new F(function(){return _v(_1h4[1],_1h6);});}},_1h7=function(_1h8,_1h9){var _1ha=new T(function(){return B(_1h2(_1h9));},1);return new F(function(){return _v(_1h8,_1ha);});};return B(_1h7(_1gf,_1ge));});return B(unAppCStr("</div>",_1gO));},1);return B(_v(B(_H(0,E(_1gJ),_11)),_1gN));});return B(unAppCStr("  <div class=\"panel-heading\"># ",_1gM));},1);return new F(function(){return _v(_1gg,_1gL);});},_1hb=function(_1hc,_){var _1hd=E(_1cU),_1he=jsFind(_1hd);if(!_1he[0]){return new F(function(){return _Bl(_1hd);});}else{var _1hf=_1he[1],_1hg=rMV(E(_1hc)),_1hh=_1hg,_1hi=new T(function(){return B(_1dL(E(E(_1hh)[7])[4]));}),_1hj=B(A(_k8,[_4b,_4Q,_1hf,_k7,_1hi,_])),_1hk=E(E(_1hh)[7])[4],_1hl=function(_1hm,_1hn,_){while(1){var _1ho=(function(_1hp,_1hq,_){var _1hr=E(_1hq);switch(_1hr[0]){case 0:var _1hs=_1hr[4],_1ht=function(_){return new F(function(){return _1hl(_1hp,_1hs,_);});};_1hm=_1ht;_1hn=_1hr[3];return null;case 1:var _1hu=_1hr[1],_1hv=new T(function(){return B(_H(0,_1hu,_11));}),_1hw=jsQuerySelectorAll(E(_1hf),toJSStr(B(unAppCStr("#edit-tactic-",_1hv)))),_1hx=function(_){var _1hy=E(_1cT),_1hz=jsFind(_1hy);if(!_1hz[0]){return new F(function(){return _Bl(_1hy);});}else{var _1hA=new T(function(){var _1hB=new T(function(){return B(_eY(_1hk,_1hu));});return B(_1gI(_1hu,_1hB));}),_1hC=B(A(_k8,[_4b,_4Q,_1hz[1],_k7,_1hA,_])),_1hD=E(_1cV)(E(_3z));return new F(function(){return _1cS(_);});}},_1hE=function(_1hF,_){return new F(function(){return _1hx(_);});},_1hG=function(_1hH,_){while(1){var _1hI=E(_1hH);if(!_1hI[0]){return _eF;}else{var _1hJ=B(A(_pa,[_4R,_4b,_46,_1hI[1],_mh,_1hE,_]));_1hH=_1hI[2];continue;}}},_1hK=B(_1hG(_1hw,_));return new F(function(){return A(_1hp,[_]);});break;default:return new F(function(){return A(_1hp,[_]);});}})(_1hm,_1hn,_);if(_1ho!=null){return _1ho;}}},_1hL=E(_1hk);if(!_1hL[0]){var _1hM=_1hL[3],_1hN=_1hL[4];if(_1hL[2]>=0){var _1hO=function(_){return new F(function(){return _1hl(_Vi,_1hN,_);});};return new F(function(){return _1hl(_1hO,_1hM,_);});}else{var _1hP=function(_){return new F(function(){return _1hl(_Vi,_1hM,_);});};return new F(function(){return _1hl(_1hP,_1hN,_);});}}else{return new F(function(){return _1hl(_Vi,_1hL,_);});}}},_1hQ=new T(function(){return [1,_1bT,_1hQ];}),_1hR=function(_){var _1hS=B(_17h(_)),_1hT=B(_1aZ(_1hS,_)),_1hU=nMV([0,_1ca,_1hT,_1hT,_1hS,_1c4,_za,_1c0]),_1hV=_1hU,_1hW=rMV(_1hV),_1hX=_1hV,_1hY=function(_1hZ,_){var _1i0=rMV(_1hV),_1i1=_1i0,_1i2=new T(function(){var _1i3=E(_1i1),_1i4=_1i3[1],_1i5=new T(function(){return B(_OD(E(_1hZ)[1],_Vh,_1i4));});return [0,_1i5,_1i3[2],_1i3[3],_1i3[4],_1i3[5],_1i3[6],_1i3[7]];}),_=wMV(_1hV,_1i2),_1i6=E(_z0),_1i7=jsFind(_1i6);if(!_1i7[0]){return new F(function(){return _Bl(_1i6);});}else{var _1i8=E(_ze),_1i9=_1i8(E(_1i7[1])),_1ia=_1i8(_1i9),_1ib=E(_1cm)(_1ia,toJSStr(E(_1cD)));if(!_1ib){return _eF;}else{var _1ic=rMV(_1hV),_1id=E(_1ic),_1ie=B(_Bo(_1hX,_1id[1],_1id[2],_1id[4],_1id[5],_1id[6],_1id[7],_)),_=wMV(_1hV,E(E(_1ie)[2]));return _eF;}}},_1if=B(A(_pa,[_4R,_4b,_r,_zb,_Vf,_1hY,_])),_1ig=function(_1ih,_){var _1ii=rMV(_1hV),_1ij=_1ii,_1ik=new T(function(){var _1il=E(_1ij),_1im=_1il[1],_1in=new T(function(){return B(_OD(E(_1ih)[1],_Ve,_1im));});return [0,_1in,_1il[2],_1il[3],_1il[4],_1il[5],_1il[6],_1il[7]];}),_=wMV(_1hV,_1ik);return _eF;},_1io=B(A(_pa,[_4R,_4b,_r,_zb,_Vg,_1ig,_])),_1ip=rMV(_1hV),_1iq=E(_1ip),_1ir=B(_Bo(_1hX,_1iq[1],_1iq[2],_1iq[4],_1iq[5],_1iq[6],_1iq[7],_)),_=wMV(_1hV,E(E(_1ir)[2])),_1is="battle",_1it=jsFind(_1is);if(!_1it[0]){return new F(function(){return _Bl(_1is);});}else{var _1iu=B(_pI(_1it[1],_1hV,_Vi,_)),_1iv="make-party",_1iw=jsFind(_1iv);if(!_1iw[0]){return new F(function(){return _Bl(_1iv);});}else{var _1ix=_1iw[1],_1iy=function(_1iz,_){while(1){var _1iA=(function(_1iB,_){var _1iC=E(_1iB);if(!_1iC[0]){return _eF;}else{var _1iD=_1iC[1],_1iE=new T(function(){return B(_1a2(_1iD));},1),_1iF=B(_mI(_1ix,_1iE,_));_1iz=_1iC[2];return null;}})(_1iz,_);if(_1iA!=null){return _1iA;}}},_1iG=function(_1iH,_1iI,_){var _1iJ=new T(function(){return B(_1a2(_1iH));},1),_1iK=B(_mI(_1ix,_1iJ,_));return new F(function(){return _1iy(_1iI,_);});},_1iL=B(_1iG(_Qd,_1cE,_)),_1iM=B(_Qf(_1hV,_)),_1iN=jsQuerySelectorAll(E(_zb),"#add-tactic-btn"),_1iO=function(_){var _1iP=rMV(_1hV),_1iQ=E(_1iP),_1iR=_1iQ[7],_1iS=new T(function(){var _1iT=E(_1iR),_1iU=_1iT[1],_1iV=_1iT[4],_1iW=new T(function(){var _1iX=new T(function(){return B(_9q(B(_1cc(_1iU,_1hQ))));});return B(_OD(B(_1cJ(_5r,B(_1cw(_1iV))))+1|0,_1iX,_1iV));});return [0,_1iU,_1iT[2],_1iT[3],_1iW];}),_=wMV(_1hV,[0,_1iQ[1],_1iQ[2],_1iQ[3],_1iQ[4],_1iQ[5],_1iQ[6],_1iS]);return new F(function(){return _1hb(_1hX,_);});},_1iY=function(_1iZ,_){return new F(function(){return _1iO(_);});},_1j0=function(_1j1,_){while(1){var _1j2=E(_1j1);if(!_1j2[0]){return _eF;}else{var _1j3=B(A(_pa,[_4R,_4b,_46,_1j2[1],_mh,_1iY,_]));_1j1=_1j2[2];continue;}}},_1j4=B(_1j0(_1iN,_));return new F(function(){return _1hb(_1hX,_);});}}},_1j5=function(_){return new F(function(){return _1hR(_);});};
var hasteMain = function() {B(A(_1j5, [0]));};window.onload = hasteMain;