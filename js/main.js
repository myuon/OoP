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

var _0="metaKey",_1="shiftKey",_2="altKey",_3="ctrlKey",_4="keyCode",_5=function(_6,_){var _7=_6[E(_4)],_8=_7,_9=_6[E(_3)],_a=_9,_b=_6[E(_2)],_c=_b,_d=_6[E(_1)],_e=_d,_f=_6[E(_0)],_g=_f;return new T(function(){var _h=Number(_8),_i=jsTrunc(_h);return [0,_i,E(_a),E(_c),E(_e),E(_g)];});},_j=function(_k,_l,_){return new F(function(){return _5(E(_l),_);});},_m="keydown",_n="keyup",_o="keypress",_p=function(_q){switch(E(_q)){case 0:return E(_o);case 1:return E(_n);default:return E(_m);}},_r=[0,_p,_j],_s=function(_t,_){return [1,_t];},_u=function(_v){return E(_v);},_w=[0,_u,_s],_x=function(_y,_z,_){var _A=B(A(_y,[_])),_B=B(A(_z,[_]));return _A;},_C=function(_D,_E,_){var _F=B(A(_D,[_])),_G=_F,_H=B(A(_E,[_])),_I=_H;return new T(function(){return B(A(_G,[_I]));});},_J=function(_K,_L,_){var _M=B(A(_L,[_]));return _K;},_N=function(_O,_P,_){var _Q=B(A(_P,[_])),_R=_Q;return new T(function(){return B(A(_O,[_R]));});},_S=[0,_N,_J],_T=function(_U,_){return _U;},_V=function(_W,_X,_){var _Y=B(A(_W,[_]));return new F(function(){return A(_X,[_]);});},_Z=[0,_S,_T,_C,_V,_x],_10=function(_11,_12,_){var _13=B(A(_11,[_]));return new F(function(){return A(_12,[_13,_]);});},_14=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_15=new T(function(){return B(unCStr("base"));}),_16=new T(function(){return B(unCStr("IOException"));}),_17=[0],_18=new T(function(){var _19=hs_wordToWord64(4053623282),_1a=hs_wordToWord64(3693590983);return [0,_19,_1a,[0,_19,_1a,_15,_14,_16],_17,_17];}),_1b=function(_1c){return E(_18);},_1d=function(_1e){return E(E(_1e)[1]);},_1f=function(_1g,_1h,_1i){var _1j=B(A(_1g,[_])),_1k=B(A(_1h,[_])),_1l=hs_eqWord64(_1j[1],_1k[1]);if(!_1l){return [0];}else{var _1m=hs_eqWord64(_1j[2],_1k[2]);return (!_1m)?[0]:[1,_1i];}},_1n=function(_1o){var _1p=E(_1o);return new F(function(){return _1f(B(_1d(_1p[1])),_1b,_1p[2]);});},_1q=new T(function(){return B(unCStr(": "));}),_1r=new T(function(){return B(unCStr(")"));}),_1s=new T(function(){return B(unCStr(" ("));}),_1t=function(_1u,_1v){var _1w=E(_1u);if(!_1w[0]){return E(_1v);}else{var _1x=_1w[2],_1y=new T(function(){return B(_1t(_1x,_1v));});return [1,_1w[1],_1y];}},_1z=new T(function(){return B(unCStr("interrupted"));}),_1A=new T(function(){return B(unCStr("system error"));}),_1B=new T(function(){return B(unCStr("unsatisified constraints"));}),_1C=new T(function(){return B(unCStr("user error"));}),_1D=new T(function(){return B(unCStr("permission denied"));}),_1E=new T(function(){return B(unCStr("illegal operation"));}),_1F=new T(function(){return B(unCStr("end of file"));}),_1G=new T(function(){return B(unCStr("resource exhausted"));}),_1H=new T(function(){return B(unCStr("resource busy"));}),_1I=new T(function(){return B(unCStr("does not exist"));}),_1J=new T(function(){return B(unCStr("already exists"));}),_1K=new T(function(){return B(unCStr("resource vanished"));}),_1L=new T(function(){return B(unCStr("timeout"));}),_1M=new T(function(){return B(unCStr("unsupported operation"));}),_1N=new T(function(){return B(unCStr("hardware fault"));}),_1O=new T(function(){return B(unCStr("inappropriate type"));}),_1P=new T(function(){return B(unCStr("invalid argument"));}),_1Q=new T(function(){return B(unCStr("failed"));}),_1R=new T(function(){return B(unCStr("protocol error"));}),_1S=function(_1T,_1U){switch(E(_1T)){case 0:return new F(function(){return _1t(_1J,_1U);});break;case 1:return new F(function(){return _1t(_1I,_1U);});break;case 2:return new F(function(){return _1t(_1H,_1U);});break;case 3:return new F(function(){return _1t(_1G,_1U);});break;case 4:return new F(function(){return _1t(_1F,_1U);});break;case 5:return new F(function(){return _1t(_1E,_1U);});break;case 6:return new F(function(){return _1t(_1D,_1U);});break;case 7:return new F(function(){return _1t(_1C,_1U);});break;case 8:return new F(function(){return _1t(_1B,_1U);});break;case 9:return new F(function(){return _1t(_1A,_1U);});break;case 10:return new F(function(){return _1t(_1R,_1U);});break;case 11:return new F(function(){return _1t(_1Q,_1U);});break;case 12:return new F(function(){return _1t(_1P,_1U);});break;case 13:return new F(function(){return _1t(_1O,_1U);});break;case 14:return new F(function(){return _1t(_1N,_1U);});break;case 15:return new F(function(){return _1t(_1M,_1U);});break;case 16:return new F(function(){return _1t(_1L,_1U);});break;case 17:return new F(function(){return _1t(_1K,_1U);});break;default:return new F(function(){return _1t(_1z,_1U);});}},_1V=new T(function(){return B(unCStr("}"));}),_1W=new T(function(){return B(unCStr("{handle: "));}),_1X=function(_1Y,_1Z,_20,_21,_22,_23){var _24=new T(function(){var _25=new T(function(){var _26=new T(function(){var _27=E(_21);if(!_27[0]){return E(_23);}else{var _28=new T(function(){var _29=new T(function(){return B(_1t(_1r,_23));},1);return B(_1t(_27,_29));},1);return B(_1t(_1s,_28));}},1);return B(_1S(_1Z,_26));},1),_2a=E(_20);if(!_2a[0]){return E(_25);}else{var _2b=new T(function(){return B(_1t(_1q,_25));},1);return B(_1t(_2a,_2b));}},1),_2c=E(_22);if(!_2c[0]){var _2d=E(_1Y);if(!_2d[0]){return E(_24);}else{var _2e=E(_2d[1]);if(!_2e[0]){var _2f=_2e[1],_2g=new T(function(){var _2h=new T(function(){var _2i=new T(function(){return B(_1t(_1q,_24));},1);return B(_1t(_1V,_2i));},1);return B(_1t(_2f,_2h));},1);return new F(function(){return _1t(_1W,_2g);});}else{var _2j=_2e[1],_2k=new T(function(){var _2l=new T(function(){var _2m=new T(function(){return B(_1t(_1q,_24));},1);return B(_1t(_1V,_2m));},1);return B(_1t(_2j,_2l));},1);return new F(function(){return _1t(_1W,_2k);});}}}else{var _2n=new T(function(){return B(_1t(_1q,_24));},1);return new F(function(){return _1t(_2c[1],_2n);});}},_2o=function(_2p){var _2q=E(_2p);return new F(function(){return _1X(_2q[1],_2q[2],_2q[3],_2q[4],_2q[6],_17);});},_2r=function(_2s,_2t,_2u){var _2v=E(_2t);return new F(function(){return _1X(_2v[1],_2v[2],_2v[3],_2v[4],_2v[6],_2u);});},_2w=function(_2x,_2y){var _2z=E(_2x);return new F(function(){return _1X(_2z[1],_2z[2],_2z[3],_2z[4],_2z[6],_2y);});},_2A=44,_2B=93,_2C=91,_2D=function(_2E,_2F,_2G){var _2H=E(_2F);if(!_2H[0]){return new F(function(){return unAppCStr("[]",_2G);});}else{var _2I=_2H[1],_2J=_2H[2],_2K=new T(function(){var _2L=new T(function(){var _2M=[1,_2B,_2G],_2N=function(_2O){var _2P=E(_2O);if(!_2P[0]){return E(_2M);}else{var _2Q=_2P[1],_2R=_2P[2],_2S=new T(function(){var _2T=new T(function(){return B(_2N(_2R));});return B(A(_2E,[_2Q,_2T]));});return [1,_2A,_2S];}};return B(_2N(_2J));});return B(A(_2E,[_2I,_2L]));});return [1,_2C,_2K];}},_2U=function(_2V,_2W){return new F(function(){return _2D(_2w,_2V,_2W);});},_2X=[0,_2r,_2o,_2U],_2Y=new T(function(){return [0,_1b,_2X,_2Z,_1n,_2o];}),_2Z=function(_30){return [0,_2Y,_30];},_31=[0],_32=7,_33=function(_34){return [0,_31,_32,_17,_34,_31,_31];},_35=function(_36,_){var _37=new T(function(){var _38=new T(function(){return B(_33(_36));});return B(_2Z(_38));});return new F(function(){return die(_37);});},_39=[0,_Z,_10,_V,_T,_35],_3a=[0,_39,_u],_3b=[0,_3a,_T],_3c=function(_3d,_3e){var _3f=jsShowI(_3d);return new F(function(){return _1t(fromJSStr(_3f),_3e);});},_3g=41,_3h=40,_3i=function(_3j,_3k,_3l){if(_3k>=0){return new F(function(){return _3c(_3k,_3l);});}else{if(_3j<=6){return new F(function(){return _3c(_3k,_3l);});}else{var _3m=new T(function(){var _3n=jsShowI(_3k);return B(_1t(fromJSStr(_3n),[1,_3g,_3l]));});return [1,_3h,_3m];}}},_3o=new T(function(){return B(unCStr(" is not an element of the map"));}),_3p=function(_3q){var _3r=new T(function(){return B(_1t(B(_3i(0,_3q,_17)),_3o));});return new F(function(){return err(B(unAppCStr("IntMap.!: key ",_3r)));});},_3s=function(_3t,_3u){var _3v=_3t;while(1){var _3w=E(_3v);switch(_3w[0]){case 0:var _3x=_3w[2]>>>0;if(((_3u>>>0&((_3x-1>>>0^4294967295)>>>0^_3x)>>>0)>>>0&4294967295)==_3w[1]){if(!((_3u>>>0&_3x)>>>0)){_3v=_3w[3];continue;}else{_3v=_3w[4];continue;}}else{return new F(function(){return _3p(_3u);});}break;case 1:if(_3u!=_3w[1]){return new F(function(){return _3p(_3u);});}else{return E(_3w[2]);}break;default:return new F(function(){return _3p(_3u);});}}},_3y=function(_3z,_3A,_3B,_3C){return (_3z!=_3B)?true:(E(_3A)!=E(_3C))?true:false;},_3D=function(_3E,_3F){var _3G=E(_3E),_3H=E(_3F);return new F(function(){return _3y(E(_3G[1]),_3G[2],E(_3H[1]),_3H[2]);});},_3I=function(_3J,_3K){return E(_3J)==E(_3K);},_3L=function(_3M,_3N,_3O,_3P){if(_3M!=_3O){return false;}else{return new F(function(){return _3I(_3N,_3P);});}},_3Q=function(_3R,_3S){var _3T=E(_3R),_3U=E(_3S);return new F(function(){return _3L(E(_3T[1]),_3T[2],E(_3U[1]),_3U[2]);});},_3V=[0,_3Q,_3D],_3W=function(_3X,_3Y){return (_3X>=_3Y)?(_3X!=_3Y)?2:1:0;},_3Z=function(_40,_41){return new F(function(){return _3W(E(_40),E(_41));});},_42=function(_43,_44,_45,_46){if(_43>=_45){if(_43!=_45){return 2;}else{return new F(function(){return _3Z(_44,_46);});}}else{return 0;}},_47=function(_48,_49){var _4a=E(_48),_4b=E(_49);return new F(function(){return _42(E(_4a[1]),_4a[2],E(_4b[1]),_4b[2]);});},_4c=function(_4d,_4e){return E(_4d)<E(_4e);},_4f=function(_4g,_4h,_4i,_4j){if(_4g>=_4i){if(_4g!=_4i){return false;}else{return new F(function(){return _4c(_4h,_4j);});}}else{return true;}},_4k=function(_4l,_4m){var _4n=E(_4l),_4o=E(_4m);return new F(function(){return _4f(E(_4n[1]),_4n[2],E(_4o[1]),_4o[2]);});},_4p=function(_4q,_4r){return E(_4q)<=E(_4r);},_4s=function(_4t,_4u,_4v,_4w){if(_4t>=_4v){if(_4t!=_4v){return false;}else{return new F(function(){return _4p(_4u,_4w);});}}else{return true;}},_4x=function(_4y,_4z){var _4A=E(_4y),_4B=E(_4z);return new F(function(){return _4s(E(_4A[1]),_4A[2],E(_4B[1]),_4B[2]);});},_4C=function(_4D,_4E){return E(_4D)>E(_4E);},_4F=function(_4G,_4H,_4I,_4J){if(_4G>=_4I){if(_4G!=_4I){return true;}else{return new F(function(){return _4C(_4H,_4J);});}}else{return false;}},_4K=function(_4L,_4M){var _4N=E(_4L),_4O=E(_4M);return new F(function(){return _4F(E(_4N[1]),_4N[2],E(_4O[1]),_4O[2]);});},_4P=function(_4Q,_4R){return E(_4Q)>=E(_4R);},_4S=function(_4T,_4U,_4V,_4W){if(_4T>=_4V){if(_4T!=_4V){return true;}else{return new F(function(){return _4P(_4U,_4W);});}}else{return false;}},_4X=function(_4Y,_4Z){var _50=E(_4Y),_51=E(_4Z);return new F(function(){return _4S(E(_50[1]),_50[2],E(_51[1]),_51[2]);});},_52=function(_53,_54){var _55=E(_53),_56=E(_55[1]),_57=E(_54),_58=E(_57[1]);return (_56>=_58)?(_56!=_58)?E(_55):(E(_55[2])>E(_57[2]))?E(_55):E(_57):E(_57);},_59=function(_5a,_5b){var _5c=E(_5a),_5d=E(_5c[1]),_5e=E(_5b),_5f=E(_5e[1]);return (_5d>=_5f)?(_5d!=_5f)?E(_5e):(E(_5c[2])>E(_5e[2]))?E(_5e):E(_5c):E(_5c);},_5g=[0,_3V,_47,_4k,_4x,_4K,_4X,_52,_59],_5h=new T(function(){return B(unCStr("Map.!: given key is not an element in the map"));}),_5i=new T(function(){return B(err(_5h));}),_5j=function(_5k,_5l,_5m){while(1){var _5n=E(_5m);if(!_5n[0]){var _5o=_5n[4],_5p=_5n[5],_5q=E(_5n[2]),_5r=E(_5q[1]);if(_5k>=_5r){if(_5k!=_5r){_5m=_5p;continue;}else{var _5s=E(_5q[2]);if(_5l>=_5s){if(_5l!=_5s){_5m=_5p;continue;}else{return E(_5n[3]);}}else{_5m=_5o;continue;}}}else{_5m=_5o;continue;}}else{return E(_5i);}}},_5t=function(_5u,_5v,_5w,_){var _5x=B(A(_5v,[_5w,_])),_5y=_5x,_5z=new T(function(){return E(E(_5y)[2]);}),_5A=new T(function(){var _5B=new T(function(){return E(E(_5y)[1]);});return B(A(_5u,[_5B]));});return [0,_5A,_5z];},_5C=function(_5D,_5E,_5F,_){var _5G=B(A(_5E,[_5F,_])),_5H=_5G,_5I=new T(function(){return E(E(_5H)[2]);});return [0,_5D,_5I];},_5J=[0,_5t,_5C],_5K=function(_5L,_5M,_5N,_){var _5O=B(A(_5L,[_5N,_])),_5P=_5O,_5Q=new T(function(){return E(E(_5P)[2]);}),_5R=B(A(_5M,[_5Q,_])),_5S=_5R,_5T=new T(function(){return E(E(_5S)[2]);}),_5U=new T(function(){var _5V=new T(function(){return E(E(_5S)[1]);});return B(A(E(_5P)[1],[_5V]));});return [0,_5U,_5T];},_5W=function(_5X,_5Y,_5Z,_){var _60=B(A(_5X,[_5Z,_])),_61=_60,_62=new T(function(){return E(E(_61)[2]);}),_63=B(A(_5Y,[_62,_])),_64=_63,_65=new T(function(){return E(E(_64)[2]);}),_66=new T(function(){return E(E(_64)[1]);});return [0,_66,_65];},_67=function(_68,_69,_6a,_){var _6b=B(A(_68,[_6a,_])),_6c=_6b,_6d=new T(function(){return E(E(_6c)[2]);}),_6e=B(A(_69,[_6d,_])),_6f=_6e,_6g=new T(function(){return E(E(_6f)[2]);}),_6h=new T(function(){return E(E(_6c)[1]);});return [0,_6h,_6g];},_6i=function(_6j,_6k,_){return [0,_6j,_6k];},_6l=[0,_5J,_6i,_5K,_5W,_67],_6m=function(_6n,_6o,_){return new F(function(){return _35(_6n,_);});},_6p=function(_6q,_6r,_6s,_){var _6t=B(A(_6q,[_6s,_])),_6u=_6t,_6v=new T(function(){return E(E(_6u)[2]);}),_6w=new T(function(){return E(E(_6u)[1]);});return new F(function(){return A(_6r,[_6w,_6v,_]);});},_6x=function(_6y){return E(E(_6y)[2]);},_6z=function(_6A,_6B,_6C,_6D,_6E){var _6F=function(_6G){var _6H=new T(function(){return E(E(_6G)[2]);}),_6I=new T(function(){return E(E(_6G)[1]);});return new F(function(){return A(_6D,[_6I,_6H]);});},_6J=new T(function(){return B(A(_6C,[_6E]));});return new F(function(){return A(_6x,[_6B,_6J,_6F]);});},_6K=function(_6L){return E(E(_6L)[5]);},_6M=function(_6N,_6O,_6P){var _6Q=new T(function(){return B(A(_6K,[_6O,_6P]));}),_6R=function(_6S){return E(_6Q);};return E(_6R);},_6T=function(_6U){return E(E(_6U)[4]);},_6V=function(_6W,_6X){var _6Y=function(_6Z){return new F(function(){return _6M(_6W,_6X,_6Z);});},_70=function(_71,_72){return new F(function(){return A(_6T,[_6X,[0,_71,_72]]);});},_73=function(_74,_6Z){return new F(function(){return _75(_6W,_6X,_74,_6Z);});},_76=function(_77,_74,_6Z){return new F(function(){return _6z(_6W,_6X,_77,_74,_6Z);});};return [0,_6W,_76,_73,_70,_6Y];},_75=function(_78,_79,_7a,_7b){var _7c=function(_7d){return E(_7b);};return new F(function(){return A(_6x,[B(_6V(_78,_79)),_7a,_7c]);});},_7e=function(_7f,_7g){return new F(function(){return _75(_6l,_39,_7f,_7g);});},_7h=[0,_6l,_6p,_7e,_6i,_6m],_7i=function(_7j,_7k,_){var _7l=B(A(_7j,[_]));return [0,_7l,_7k];},_7m=[0,_7h,_7i],_7n=new T(function(){return B(unCStr("&nbsp;"));}),_7o=new T(function(){return B(unCStr("@"));}),_7p=new T(function(){return B(_1t(_7n,_7o));}),_7q=function(_7r){var _7s=E(_7r);if(_7s==1){return E(_7p);}else{var _7t=new T(function(){return B(_7q(_7s-1|0));},1);return new F(function(){return _1t(_7n,_7t);});}},_7u="dungeon-field",_7v=function(_7w,_7x,_7y){while(1){var _7z=E(_7y);if(!_7z[0]){var _7A=_7z[4],_7B=_7z[5],_7C=E(_7z[2]),_7D=E(_7C[1]);if(_7w>=_7D){if(_7w!=_7D){_7y=_7B;continue;}else{var _7E=E(_7x),_7F=E(_7C[2]);if(_7E>=_7F){if(_7E!=_7F){_7x=_7E;_7y=_7B;continue;}else{return E(_7z[3]);}}else{_7x=_7E;_7y=_7A;continue;}}}else{_7y=_7A;continue;}}else{return E(_5i);}}},_7G=new T(function(){return B(unCStr("<br>"));}),_7H=function(_7I,_7J){if(_7I<=_7J){var _7K=function(_7L){var _7M=new T(function(){if(_7L!=_7J){return B(_7K(_7L+1|0));}else{return [0];}});return [1,_7L,_7M];};return new F(function(){return _7K(_7I);});}else{return [0];}},_7N=new T(function(){return B(_7H(0,24));}),_7O=new T(function(){return B(_7H(0,74));}),_7P=function(_7Q){var _7R=E(_7Q);if(!_7R[0]){return [0];}else{var _7S=_7R[2],_7T=E(_7R[1]);if(E(_7T)==32){var _7U=new T(function(){return B(_7P(_7S));},1);return new F(function(){return _1t(_7n,_7U);});}else{var _7V=new T(function(){return B(_7P(_7S));},1);return new F(function(){return _1t([1,_7T,_17],_7V);});}}},_7W=function(_7X){var _7Y=E(_7X);if(!_7Y[0]){return [0];}else{var _7Z=_7Y[2],_80=new T(function(){return B(_7W(_7Z));},1);return new F(function(){return _1t(_7Y[1],_80);});}},_81=function(_82,_83){var _84=E(_83);if(!_84[0]){return [0];}else{var _85=_84[1],_86=_84[2],_87=new T(function(){return B(_81(_82,_86));}),_88=new T(function(){return B(A(_82,[_85]));});return [1,_88,_87];}},_89=function(_8a,_8b){var _8c=E(_8b);if(!_8c[0]){return [0];}else{var _8d=_8c[2],_8e=new T(function(){return B(_89(_8a,_8d));});return [1,_8a,[1,_8c[1],_8e]];}},_8f=function(_8g){var _8h=function(_8i){var _8j=function(_8k,_8l){var _8m=E(_8k);if(!_8m[0]){return [0];}else{var _8n=_8m[1],_8o=_8m[2],_8p=E(_8l);if(_8p==1){var _8q=new T(function(){return B(_7v(E(_8n),_8i,_8g));});return [1,_8q,_17];}else{var _8r=new T(function(){return B(_8j(_8o,_8p-1|0));}),_8s=new T(function(){return B(_7v(E(_8n),_8i,_8g));});return [1,_8s,_8r];}}};return new F(function(){return _8j(_7O,30);});},_8t=B(_81(_8h,_7N));if(!_8t[0]){return [0];}else{var _8u=_8t[2],_8v=new T(function(){return B(_89(_7G,_8u));});return new F(function(){return _7P(B(_7W([1,_8t[1],_8v])));});}},_8w=[1],_8x=new T(function(){return B(unCStr("Failure in Data.Map.balanceL"));}),_8y=function(_8z){return new F(function(){return err(_8x);});},_8A=new T(function(){return B(_8y(_));}),_8B=function(_8C,_8D,_8E,_8F){var _8G=E(_8F);if(!_8G[0]){var _8H=_8G[1],_8I=E(_8E);if(!_8I[0]){var _8J=_8I[1],_8K=_8I[2],_8L=_8I[3];if(_8J<=(imul(3,_8H)|0)){return [0,(1+_8J|0)+_8H|0,E(_8C),_8D,E(_8I),E(_8G)];}else{var _8M=E(_8I[4]);if(!_8M[0]){var _8N=_8M[1],_8O=E(_8I[5]);if(!_8O[0]){var _8P=_8O[1],_8Q=_8O[2],_8R=_8O[3],_8S=_8O[4],_8T=_8O[5];if(_8P>=(imul(2,_8N)|0)){var _8U=function(_8V){var _8W=E(_8T);return (_8W[0]==0)?[0,(1+_8J|0)+_8H|0,E(_8Q),_8R,[0,(1+_8N|0)+_8V|0,E(_8K),_8L,E(_8M),E(_8S)],[0,(1+_8H|0)+_8W[1]|0,E(_8C),_8D,E(_8W),E(_8G)]]:[0,(1+_8J|0)+_8H|0,E(_8Q),_8R,[0,(1+_8N|0)+_8V|0,E(_8K),_8L,E(_8M),E(_8S)],[0,1+_8H|0,E(_8C),_8D,E(_8w),E(_8G)]];},_8X=E(_8S);if(!_8X[0]){return new F(function(){return _8U(_8X[1]);});}else{return new F(function(){return _8U(0);});}}else{return [0,(1+_8J|0)+_8H|0,E(_8K),_8L,E(_8M),[0,(1+_8H|0)+_8P|0,E(_8C),_8D,E(_8O),E(_8G)]];}}else{return E(_8A);}}else{return E(_8A);}}}else{return [0,1+_8H|0,E(_8C),_8D,E(_8w),E(_8G)];}}else{var _8Y=E(_8E);if(!_8Y[0]){var _8Z=_8Y[1],_90=_8Y[2],_91=_8Y[3],_92=_8Y[5],_93=E(_8Y[4]);if(!_93[0]){var _94=_93[1],_95=E(_92);if(!_95[0]){var _96=_95[1],_97=_95[2],_98=_95[3],_99=_95[4],_9a=_95[5];if(_96>=(imul(2,_94)|0)){var _9b=function(_9c){var _9d=E(_9a);return (_9d[0]==0)?[0,1+_8Z|0,E(_97),_98,[0,(1+_94|0)+_9c|0,E(_90),_91,E(_93),E(_99)],[0,1+_9d[1]|0,E(_8C),_8D,E(_9d),E(_8w)]]:[0,1+_8Z|0,E(_97),_98,[0,(1+_94|0)+_9c|0,E(_90),_91,E(_93),E(_99)],[0,1,E(_8C),_8D,E(_8w),E(_8w)]];},_9e=E(_99);if(!_9e[0]){return new F(function(){return _9b(_9e[1]);});}else{return new F(function(){return _9b(0);});}}else{return [0,1+_8Z|0,E(_90),_91,E(_93),[0,1+_96|0,E(_8C),_8D,E(_95),E(_8w)]];}}else{return [0,3,E(_90),_91,E(_93),[0,1,E(_8C),_8D,E(_8w),E(_8w)]];}}else{var _9f=E(_92);return (_9f[0]==0)?[0,3,E(_9f[2]),_9f[3],[0,1,E(_90),_91,E(_8w),E(_8w)],[0,1,E(_8C),_8D,E(_8w),E(_8w)]]:[0,2,E(_8C),_8D,E(_8Y),E(_8w)];}}else{return [0,1,E(_8C),_8D,E(_8w),E(_8w)];}}},_9g=new T(function(){return B(unCStr("Failure in Data.Map.balanceR"));}),_9h=function(_9i){return new F(function(){return err(_9g);});},_9j=new T(function(){return B(_9h(_));}),_9k=function(_9l,_9m,_9n,_9o){var _9p=E(_9n);if(!_9p[0]){var _9q=_9p[1],_9r=E(_9o);if(!_9r[0]){var _9s=_9r[1],_9t=_9r[2],_9u=_9r[3];if(_9s<=(imul(3,_9q)|0)){return [0,(1+_9q|0)+_9s|0,E(_9l),_9m,E(_9p),E(_9r)];}else{var _9v=E(_9r[4]);if(!_9v[0]){var _9w=_9v[1],_9x=_9v[2],_9y=_9v[3],_9z=_9v[4],_9A=_9v[5],_9B=E(_9r[5]);if(!_9B[0]){var _9C=_9B[1];if(_9w>=(imul(2,_9C)|0)){var _9D=function(_9E){var _9F=E(_9l),_9G=E(_9A);return (_9G[0]==0)?[0,(1+_9q|0)+_9s|0,E(_9x),_9y,[0,(1+_9q|0)+_9E|0,E(_9F),_9m,E(_9p),E(_9z)],[0,(1+_9C|0)+_9G[1]|0,E(_9t),_9u,E(_9G),E(_9B)]]:[0,(1+_9q|0)+_9s|0,E(_9x),_9y,[0,(1+_9q|0)+_9E|0,E(_9F),_9m,E(_9p),E(_9z)],[0,1+_9C|0,E(_9t),_9u,E(_8w),E(_9B)]];},_9H=E(_9z);if(!_9H[0]){return new F(function(){return _9D(_9H[1]);});}else{return new F(function(){return _9D(0);});}}else{return [0,(1+_9q|0)+_9s|0,E(_9t),_9u,[0,(1+_9q|0)+_9w|0,E(_9l),_9m,E(_9p),E(_9v)],E(_9B)];}}else{return E(_9j);}}else{return E(_9j);}}}else{return [0,1+_9q|0,E(_9l),_9m,E(_9p),E(_8w)];}}else{var _9I=E(_9o);if(!_9I[0]){var _9J=_9I[1],_9K=_9I[2],_9L=_9I[3],_9M=_9I[5],_9N=E(_9I[4]);if(!_9N[0]){var _9O=_9N[1],_9P=_9N[2],_9Q=_9N[3],_9R=_9N[4],_9S=_9N[5],_9T=E(_9M);if(!_9T[0]){var _9U=_9T[1];if(_9O>=(imul(2,_9U)|0)){var _9V=function(_9W){var _9X=E(_9l),_9Y=E(_9S);return (_9Y[0]==0)?[0,1+_9J|0,E(_9P),_9Q,[0,1+_9W|0,E(_9X),_9m,E(_8w),E(_9R)],[0,(1+_9U|0)+_9Y[1]|0,E(_9K),_9L,E(_9Y),E(_9T)]]:[0,1+_9J|0,E(_9P),_9Q,[0,1+_9W|0,E(_9X),_9m,E(_8w),E(_9R)],[0,1+_9U|0,E(_9K),_9L,E(_8w),E(_9T)]];},_9Z=E(_9R);if(!_9Z[0]){return new F(function(){return _9V(_9Z[1]);});}else{return new F(function(){return _9V(0);});}}else{return [0,1+_9J|0,E(_9K),_9L,[0,1+_9O|0,E(_9l),_9m,E(_8w),E(_9N)],E(_9T)];}}else{return [0,3,E(_9P),_9Q,[0,1,E(_9l),_9m,E(_8w),E(_8w)],[0,1,E(_9K),_9L,E(_8w),E(_8w)]];}}else{var _a0=E(_9M);return (_a0[0]==0)?[0,3,E(_9K),_9L,[0,1,E(_9l),_9m,E(_8w),E(_8w)],E(_a0)]:[0,2,E(_9l),_9m,E(_8w),E(_9I)];}}else{return [0,1,E(_9l),_9m,E(_8w),E(_8w)];}}},_a1=function(_a2){return E(E(_a2)[2]);},_a3=function(_a4,_a5,_a6,_a7){var _a8=E(_a5),_a9=E(_a7);if(!_a9[0]){var _aa=_a9[2],_ab=_a9[3],_ac=_a9[4],_ad=_a9[5];switch(B(A(_a1,[_a4,_a8,_aa]))){case 0:return new F(function(){return _8B(_aa,_ab,B(_a3(_a4,_a8,_a6,_ac)),_ad);});break;case 1:return [0,_a9[1],E(_a8),_a6,E(_ac),E(_ad)];default:return new F(function(){return _9k(_aa,_ab,_ac,B(_a3(_a4,_a8,_a6,_ad)));});}}else{return [0,1,E(_a8),_a6,E(_8w),E(_8w)];}},_ae=function(_af,_ag,_ah,_ai){return new F(function(){return _a3(_af,_ag,_ah,_ai);});},_aj=function(_ak,_al,_am){var _an=function(_ao){var _ap=E(_ao);if(!_ap[0]){return E(_am);}else{var _aq=E(_ap[1]);return new F(function(){return _ae(_ak,_aq[1],_aq[2],B(_an(_ap[2])));});}};return new F(function(){return _an(_al);});},_ar=new T(function(){return B(unCStr("innerHTML"));}),_as=[1,_17,_17],_at=function(_au){var _av=E(_au);if(!_av[0]){return E(_as);}else{var _aw=_av[2],_ax=new T(function(){return B(_at(_aw));}),_ay=function(_az){var _aA=E(_az);if(!_aA[0]){return [0];}else{var _aB=_aA[1],_aC=_aA[2],_aD=new T(function(){return B(_ay(_aC));}),_aE=function(_aF){var _aG=E(_aF);if(!_aG[0]){return E(_aD);}else{var _aH=_aG[2],_aI=new T(function(){return B(_aE(_aH));});return [1,[1,_aB,_aG[1]],_aI];}};return new F(function(){return _aE(_ax);});}};return new F(function(){return _ay(_av[1]);});}},_aJ=function(_aK,_aL){if(0>=_aK){return E(_as);}else{var _aM=[1,_aL,_17],_aN=function(_aO){var _aP=E(_aO);if(_aP==1){return E(_aM);}else{var _aQ=new T(function(){return B(_aN(_aP-1|0));});return [1,_aL,_aQ];}};return new F(function(){return _at(B(_aN(_aK)));});}},_aR=-1,_aS=0,_aT=1,_aU=[1,_aT,_17],_aV=[1,_aS,_aU],_aW=[1,_aR,_aV],_aX=new T(function(){return B(_aJ(2,_aW));}),_aY=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:119:3-9"));}),_aZ=[0,_31,_32,_17,_aY,_31,_31],_b0=new T(function(){return B(_2Z(_aZ));}),_b1=0,_b2=function(_b3){return E(E(_b3)[1]);},_b4=function(_b5){return E(E(_b5)[2]);},_b6=function(_b7,_b8,_b9,_ba,_bb){var _bc=function(_){var _bd=jsSet(B(A(_b2,[_b7,_b9])),toJSStr(E(_ba)),toJSStr(E(_bb)));return _b1;};return new F(function(){return A(_b4,[_b8,_bc]);});},_be=new T(function(){return B(unCStr(" found!"));}),_bf=function(_bg){var _bh=new T(function(){return B(_1t(fromJSStr(E(_bg)),_be));});return new F(function(){return err(B(unAppCStr("No element with ID ",_bh)));});},_bi=function(_,_bj,_bk,_bl,_bm,_bn,_bo){var _bp=jsFind("player");if(!_bp[0]){return new F(function(){return die(_b0);});}else{var _bq=new T(function(){var _br=function(_bs){while(1){var _bt=(function(_bu){var _bv=E(_bu);if(!_bv[0]){return [0];}else{var _bw=_bv[2],_bx=E(_bv[1]);if(!_bx[0]){_bs=_bw;return null;}else{var _by=E(_bx[2]);if(!_by[0]){_bs=_bw;return null;}else{if(!E(_by[2])[0]){var _bz=E(_bk),_bA=E(_bx[1]);if(0>(_bz+_bA|0)){var _bB=function(_bC){while(1){var _bD=(function(_bE){var _bF=E(_bE);if(!_bF[0]){return [0];}else{var _bG=_bF[2],_bH=E(_bF[1]);if(!_bH[0]){_bC=_bG;return null;}else{var _bI=E(_bH[2]);if(!_bI[0]){_bC=_bG;return null;}else{if(!E(_bI[2])[0]){var _bJ=E(_bH[1]);if(0>(_bz+_bJ|0)){_bC=_bG;return null;}else{if((_bz+_bJ|0)>74){_bC=_bG;return null;}else{var _bK=E(_bl),_bL=E(_bI[1]);if(0>(_bK+_bL|0)){_bC=_bG;return null;}else{if((_bK+_bL|0)>24){_bC=_bG;return null;}else{var _bM=new T(function(){return B(_bB(_bG));}),_bN=_bz+_bJ|0,_bO=_bK+_bL|0,_bP=new T(function(){return B(_5j(_bN,_bO,_bn));});return [1,[0,[0,_bN,_bO],_bP],_bM];}}}}}else{_bC=_bG;return null;}}}}})(_bC);if(_bD!=null){return _bD;}}};return new F(function(){return _bB(_bw);});}else{if((_bz+_bA|0)>74){var _bQ=function(_bR){while(1){var _bS=(function(_bT){var _bU=E(_bT);if(!_bU[0]){return [0];}else{var _bV=_bU[2],_bW=E(_bU[1]);if(!_bW[0]){_bR=_bV;return null;}else{var _bX=E(_bW[2]);if(!_bX[0]){_bR=_bV;return null;}else{if(!E(_bX[2])[0]){var _bY=E(_bW[1]);if(0>(_bz+_bY|0)){_bR=_bV;return null;}else{if((_bz+_bY|0)>74){_bR=_bV;return null;}else{var _bZ=E(_bl),_c0=E(_bX[1]);if(0>(_bZ+_c0|0)){_bR=_bV;return null;}else{if((_bZ+_c0|0)>24){_bR=_bV;return null;}else{var _c1=new T(function(){return B(_bQ(_bV));}),_c2=_bz+_bY|0,_c3=_bZ+_c0|0,_c4=new T(function(){return B(_5j(_c2,_c3,_bn));});return [1,[0,[0,_c2,_c3],_c4],_c1];}}}}}else{_bR=_bV;return null;}}}}})(_bR);if(_bS!=null){return _bS;}}};return new F(function(){return _bQ(_bw);});}else{var _c5=E(_bl),_c6=E(_by[1]);if(0>(_c5+_c6|0)){var _c7=function(_c8){while(1){var _c9=(function(_ca){var _cb=E(_ca);if(!_cb[0]){return [0];}else{var _cc=_cb[2],_cd=E(_cb[1]);if(!_cd[0]){_c8=_cc;return null;}else{var _ce=E(_cd[2]);if(!_ce[0]){_c8=_cc;return null;}else{if(!E(_ce[2])[0]){var _cf=E(_cd[1]);if(0>(_bz+_cf|0)){_c8=_cc;return null;}else{if((_bz+_cf|0)>74){_c8=_cc;return null;}else{var _cg=E(_ce[1]);if(0>(_c5+_cg|0)){_c8=_cc;return null;}else{if((_c5+_cg|0)>24){_c8=_cc;return null;}else{var _ch=new T(function(){return B(_c7(_cc));}),_ci=_bz+_cf|0,_cj=_c5+_cg|0,_ck=new T(function(){return B(_5j(_ci,_cj,_bn));});return [1,[0,[0,_ci,_cj],_ck],_ch];}}}}}else{_c8=_cc;return null;}}}}})(_c8);if(_c9!=null){return _c9;}}};return new F(function(){return _c7(_bw);});}else{if((_c5+_c6|0)>24){var _cl=function(_cm){while(1){var _cn=(function(_co){var _cp=E(_co);if(!_cp[0]){return [0];}else{var _cq=_cp[2],_cr=E(_cp[1]);if(!_cr[0]){_cm=_cq;return null;}else{var _cs=E(_cr[2]);if(!_cs[0]){_cm=_cq;return null;}else{if(!E(_cs[2])[0]){var _ct=E(_cr[1]);if(0>(_bz+_ct|0)){_cm=_cq;return null;}else{if((_bz+_ct|0)>74){_cm=_cq;return null;}else{var _cu=E(_cs[1]);if(0>(_c5+_cu|0)){_cm=_cq;return null;}else{if((_c5+_cu|0)>24){_cm=_cq;return null;}else{var _cv=new T(function(){return B(_cl(_cq));}),_cw=_bz+_ct|0,_cx=_c5+_cu|0,_cy=new T(function(){return B(_5j(_cw,_cx,_bn));});return [1,[0,[0,_cw,_cx],_cy],_cv];}}}}}else{_cm=_cq;return null;}}}}})(_cm);if(_cn!=null){return _cn;}}};return new F(function(){return _cl(_bw);});}else{var _cz=new T(function(){var _cA=function(_cB){while(1){var _cC=(function(_cD){var _cE=E(_cD);if(!_cE[0]){return [0];}else{var _cF=_cE[2],_cG=E(_cE[1]);if(!_cG[0]){_cB=_cF;return null;}else{var _cH=E(_cG[2]);if(!_cH[0]){_cB=_cF;return null;}else{if(!E(_cH[2])[0]){var _cI=E(_cG[1]);if(0>(_bz+_cI|0)){_cB=_cF;return null;}else{if((_bz+_cI|0)>74){_cB=_cF;return null;}else{var _cJ=E(_cH[1]);if(0>(_c5+_cJ|0)){_cB=_cF;return null;}else{if((_c5+_cJ|0)>24){_cB=_cF;return null;}else{var _cK=new T(function(){return B(_cA(_cF));}),_cL=_bz+_cI|0,_cM=_c5+_cJ|0,_cN=new T(function(){return B(_5j(_cL,_cM,_bn));});return [1,[0,[0,_cL,_cM],_cN],_cK];}}}}}else{_cB=_cF;return null;}}}}})(_cB);if(_cC!=null){return _cC;}}};return B(_cA(_bw));}),_cO=_bz+_bA|0,_cP=_c5+_c6|0,_cQ=new T(function(){return B(_5j(_cO,_cP,_bn));});return [1,[0,[0,_cO,_cP],_cQ],_cz];}}}}}else{_bs=_bw;return null;}}}}})(_bs);if(_bt!=null){return _bt;}}};return B(_aj(_5g,B(_br(_aX)),_bo));}),_cR=new T(function(){var _cS=E(_bl);if(0>=_cS){var _cT=E(_bk);if(0>=_cT){return E(_7o);}else{return B(_7q(_cT));}}else{var _cU=new T(function(){var _cV=new T(function(){var _cW=E(_bk);if(0>=_cW){return E(_7o);}else{return B(_7q(_cW));}},1);return B(_1t(_7G,_cV));}),_cX=function(_cY){var _cZ=E(_cY);if(_cZ==1){return E(_cU);}else{var _d0=new T(function(){return B(_cX(_cZ-1|0));},1);return new F(function(){return _1t(_7G,_d0);});}};return B(_cX(_cS));}}),_d1=B(A(_b6,[_w,_7m,_bp[1],_ar,_cR,[0,_bj,[0,_bk,_bl],_bm,_bn,_bq],_])),_d2=_d1,_d3=E(_7u),_d4=jsFind(_d3);if(!_d4[0]){return new F(function(){return _bf(_d3);});}else{var _d5=new T(function(){return E(E(_d2)[2]);}),_d6=new T(function(){var _d7=new T(function(){return E(E(_d5)[5]);});return B(_8f(_d7));});return new F(function(){return A(_b6,[_w,_7m,_d4[1],_ar,_d6,_d5,_]);});}}},_d8=function(_d9,_da,_db,_dc,_dd,_){var _de=E(_db),_df=_de[1],_dg=_de[2],_dh=function(_,_di,_dj,_dk,_dl,_dm,_dn){var _do=function(_,_dp,_dq,_dr,_ds,_dt,_du){var _dv=function(_,_dw,_dx,_dy,_dz,_dA,_dB){if(!B(_3s(_da,39))){return new F(function(){return _bi(_,_dw,_dx,_dy,_dz,_dA,_dB);});}else{var _dC=new T(function(){return E(_dx)+1|0;});return new F(function(){return _bi(_,_dw,_dC,_dy,_dz,_dA,_dB);});}};if(!B(_3s(_da,37))){return new F(function(){return _dv(_,_dp,_dq,_dr,_ds,_dt,_du);});}else{var _dD=new T(function(){return E(_dq)-1|0;});return new F(function(){return _dv(_,_dp,_dD,_dr,_ds,_dt,_du);});}};if(!B(_3s(_da,40))){return new F(function(){return _do(_,_di,_dj,_dk,_dl,_dm,_dn);});}else{var _dE=new T(function(){return E(_dk)+1|0;});return new F(function(){return _do(_,_di,_dj,_dE,_dl,_dm,_dn);});}};if(!B(_3s(_da,38))){return new F(function(){return _dh(_,_da,_df,_dg,_d9,_dc,_dd);});}else{var _dF=new T(function(){return E(_dg)-1|0;});return new F(function(){return _dh(_,_da,_df,_dF,_d9,_dc,_dd);});}},_dG=function(_dH,_dI,_dJ){var _dK=E(_dJ);switch(_dK[0]){case 0:var _dL=_dK[1],_dM=_dK[2],_dN=_dK[3],_dO=_dK[4],_dP=_dM>>>0;if(((_dH>>>0&((_dP-1>>>0^4294967295)>>>0^_dP)>>>0)>>>0&4294967295)==_dL){return ((_dH>>>0&_dP)>>>0==0)?[0,_dL,_dM,E(B(_dG(_dH,_dI,_dN))),E(_dO)]:[0,_dL,_dM,E(_dN),E(B(_dG(_dH,_dI,_dO)))];}else{var _dQ=(_dH>>>0^_dL>>>0)>>>0,_dR=(_dQ|_dQ>>>1)>>>0,_dS=(_dR|_dR>>>2)>>>0,_dT=(_dS|_dS>>>4)>>>0,_dU=(_dT|_dT>>>8)>>>0,_dV=(_dU|_dU>>>16)>>>0,_dW=(_dV^_dV>>>1)>>>0&4294967295,_dX=_dW>>>0;return ((_dH>>>0&_dX)>>>0==0)?[0,(_dH>>>0&((_dX-1>>>0^4294967295)>>>0^_dX)>>>0)>>>0&4294967295,_dW,[1,_dH,_dI],E(_dK)]:[0,(_dH>>>0&((_dX-1>>>0^4294967295)>>>0^_dX)>>>0)>>>0&4294967295,_dW,E(_dK),[1,_dH,_dI]];}break;case 1:var _dY=_dK[1];if(_dH!=_dY){var _dZ=(_dH>>>0^_dY>>>0)>>>0,_e0=(_dZ|_dZ>>>1)>>>0,_e1=(_e0|_e0>>>2)>>>0,_e2=(_e1|_e1>>>4)>>>0,_e3=(_e2|_e2>>>8)>>>0,_e4=(_e3|_e3>>>16)>>>0,_e5=(_e4^_e4>>>1)>>>0&4294967295,_e6=_e5>>>0;return ((_dH>>>0&_e6)>>>0==0)?[0,(_dH>>>0&((_e6-1>>>0^4294967295)>>>0^_e6)>>>0)>>>0&4294967295,_e5,[1,_dH,_dI],E(_dK)]:[0,(_dH>>>0&((_e6-1>>>0^4294967295)>>>0^_e6)>>>0)>>>0&4294967295,_e5,E(_dK),[1,_dH,_dI]];}else{return [1,_dH,_dI];}break;default:return [1,_dH,_dI];}},_e7=false,_e8=0,_e9=1,_ea=true,_eb=function(_ec,_ed){while(1){var _ee=E(_ed);if(!_ee[0]){return [0];}else{var _ef=_ee[2],_eg=E(_ec);if(_eg==1){return E(_ef);}else{_ec=_eg-1|0;_ed=_ef;continue;}}}},_eh=function(_ei,_ej,_ek){var _el=E(_ei);if(_el==1){return E(_ek);}else{return new F(function(){return _eb(_el-1|0,_ek);});}},_em=function(_en,_eo){var _ep=E(_eo);if(!_ep[0]){return [0];}else{var _eq=_ep[1],_er=_ep[2],_es=E(_en);if(_es==1){return [1,_eq,_17];}else{var _et=new T(function(){return B(_em(_es-1|0,_er));});return [1,_eq,_et];}}},_eu=function(_ev,_ew,_ex){var _ey=new T(function(){if(_ev>0){return B(_ez(_ev,B(_eh(_ev,_ew,_ex))));}else{return B(_eu(_ev,_ew,_ex));}}),_eA=new T(function(){if(0>=_ev){return [0];}else{return B(_em(_ev,[1,_ew,_ex]));}});return [1,_eA,_ey];},_ez=function(_eB,_eC){var _eD=E(_eC);if(!_eD[0]){return [0];}else{var _eE=_eD[1],_eF=_eD[2],_eG=new T(function(){if(_eB>0){return B(_ez(_eB,B(_eh(_eB,_eE,_eF))));}else{return B(_eu(_eB,_eE,_eF));}}),_eH=new T(function(){if(0>=_eB){return [0];}else{return B(_em(_eB,_eD));}});return [1,_eH,_eG];}},_eI=function(_eJ,_eK,_eL,_eM){var _eN=E(_eM);if(!_eN[0]){var _eO=_eN[3],_eP=_eN[4],_eQ=_eN[5],_eR=E(_eN[2]),_eS=E(_eJ),_eT=E(_eR[1]);if(_eS>=_eT){if(_eS!=_eT){return new F(function(){return _9k(_eR,_eO,_eP,B(_eI(_eS,_eK,_eL,_eQ)));});}else{var _eU=E(_eK),_eV=E(_eR[2]);if(_eU>=_eV){if(_eU!=_eV){return new F(function(){return _9k(_eR,_eO,_eP,B(_eI(_eS,_eU,_eL,_eQ)));});}else{return [0,_eN[1],[0,_eS,_eU],_eL,E(_eP),E(_eQ)];}}else{return new F(function(){return _8B(_eR,_eO,B(_eI(_eS,_eU,_eL,_eP)),_eQ);});}}}else{return new F(function(){return _8B(_eR,_eO,B(_eI(_eS,_eK,_eL,_eP)),_eQ);});}}else{return [0,1,[0,_eJ,_eK],_eL,E(_8w),E(_8w)];}},_eW=function(_eX){var _eY=E(_eX);if(!_eY[0]){return [0];}else{var _eZ=_eY[2],_f0=new T(function(){return B(_eW(_eZ));},1);return new F(function(){return _1t(_eY[1],_f0);});}},_f1=function(_f2){return new F(function(){return _eW(_f2);});},_f3=function(_f4,_){return new T(function(){var _f5=Number(E(_f4));return jsTrunc(_f5);});},_f6=new T(function(){return B(unCStr("GHC.Exception"));}),_f7=new T(function(){return B(unCStr("base"));}),_f8=new T(function(){return B(unCStr("ArithException"));}),_f9=new T(function(){var _fa=hs_wordToWord64(4194982440),_fb=hs_wordToWord64(3110813675);return [0,_fa,_fb,[0,_fa,_fb,_f7,_f6,_f8],_17,_17];}),_fc=function(_fd){return E(_f9);},_fe=function(_ff){var _fg=E(_ff);return new F(function(){return _1f(B(_1d(_fg[1])),_fc,_fg[2]);});},_fh=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_fi=new T(function(){return B(unCStr("denormal"));}),_fj=new T(function(){return B(unCStr("divide by zero"));}),_fk=new T(function(){return B(unCStr("loss of precision"));}),_fl=new T(function(){return B(unCStr("arithmetic underflow"));}),_fm=new T(function(){return B(unCStr("arithmetic overflow"));}),_fn=function(_fo,_fp){switch(E(_fo)){case 0:return new F(function(){return _1t(_fm,_fp);});break;case 1:return new F(function(){return _1t(_fl,_fp);});break;case 2:return new F(function(){return _1t(_fk,_fp);});break;case 3:return new F(function(){return _1t(_fj,_fp);});break;case 4:return new F(function(){return _1t(_fi,_fp);});break;default:return new F(function(){return _1t(_fh,_fp);});}},_fq=function(_fr){return new F(function(){return _fn(_fr,_17);});},_fs=function(_ft,_fu,_fv){return new F(function(){return _fn(_fu,_fv);});},_fw=function(_fx,_fy){return new F(function(){return _2D(_fn,_fx,_fy);});},_fz=[0,_fs,_fq,_fw],_fA=new T(function(){return [0,_fc,_fz,_fB,_fe,_fq];}),_fB=function(_fC){return [0,_fA,_fC];},_fD=3,_fE=new T(function(){return B(_fB(_fD));}),_fF=new T(function(){return die(_fE);}),_fG=(function(s){return s[0];}),_fH=function(_fI,_fJ){var _fK=_fI%_fJ;if(_fI<=0){if(_fI>=0){return E(_fK);}else{if(_fJ<=0){return E(_fK);}else{var _fL=E(_fK);return (_fL==0)?0:_fL+_fJ|0;}}}else{if(_fJ>=0){if(_fI>=0){return E(_fK);}else{if(_fJ<=0){return E(_fK);}else{var _fM=E(_fK);return (_fM==0)?0:_fM+_fJ|0;}}}else{var _fN=E(_fK);return (_fN==0)?0:_fN+_fJ|0;}}},_fO=(function(s){var ba = window['newByteArr'](16);ba['v']['w32'][0] = s[0];ba['v']['w32'][1] = s[1];ba['v']['w32'][2] = s[2];ba['v']['w32'][3] = s[3];return window['md51'](ba,16);}),_fP=function(_fQ){var _fR=B(A(_fQ,[_]));return E(_fR);},_fS=function(_fT){var _fU=function(_){return new F(function(){return E(_fO)(E(_fT));});};return new F(function(){return _fP(_fU);});},_fV=function(_fW,_fX,_fY){while(1){var _fZ=(function(_g0,_g1,_g2){if(_g0>_g1){var _g3=_g1,_g4=_g0,_g5=_g2;_fW=_g3;_fX=_g4;_fY=_g5;return null;}else{var _g6=new T(function(){return B(_fS(_g2));}),_g7=new T(function(){var _g8=(_g1-_g0|0)+1|0;switch(_g8){case -1:return _g0;break;case 0:return E(_fF);break;default:var _g9=function(_){var _ga=E(_fG)(E(_g2));return new F(function(){return _f3(_ga,0);});};return B(_fH(B(_fP(_g9)),_g8))+_g0|0;}});return [0,_g7,_g6];}})(_fW,_fX,_fY);if(_fZ!=null){return _fZ;}}},_gb=(function(){var ba = window['newByteArr'](16);ba['v']['f64'][0] = Math.random();ba['v']['f64'][1] = Math.random();return window['md51'](ba,16);}),_gc=function(_gd,_){while(1){var _ge=(function(_gf,_){var _gg=E(_gf);if(!_gg[0]){return _17;}else{var _gh=_gg[2],_gi=E(_gg[1]);if(!_gi[0]){_gd=_gh;return null;}else{var _gj=_gi[2],_gk=E(_gi[1]),_gl=E(_gk[1]),_gm=E(_gk[2]),_gn=E(_gb),_go=_gn(),_gp=_go,_gq=E(_gm[2]),_gr=E(_gl[2]);if((_gq-_gr|0)<4){var _gs=function(_gt,_){var _gu=E(_gt);if(!_gu[0]){return new F(function(){return _gc(_gh,_);});}else{var _gv=_gu[2],_gw=E(_gu[1]),_gx=E(_gw[1]),_gy=E(_gw[2]),_gz=_gn(),_gA=_gz,_gB=E(_gy[2]),_gC=E(_gx[2]);if((_gB-_gC|0)<4){var _gD=B(_gs(_gv,_));return [1,_17,_gD];}else{var _gE=B(_gs(_gv,_)),_gF=new T(function(){return E(B(_fV((_gC+2|0)+1|0,(_gB-2|0)-1|0,_gA))[1]);});return [1,[1,[0,_gx,[0,_gy[1],_gF]],[1,[0,[0,_gx[1],_gF],_gy],_17]],_gE];}}},_gG=B(_gs(_gj,_));return [1,_17,_gG];}else{var _gH=function(_gI,_){var _gJ=E(_gI);if(!_gJ[0]){return new F(function(){return _gc(_gh,_);});}else{var _gK=_gJ[2],_gL=E(_gJ[1]),_gM=E(_gL[1]),_gN=E(_gL[2]),_gO=_gn(),_gP=_gO,_gQ=E(_gN[2]),_gR=E(_gM[2]);if((_gQ-_gR|0)<4){var _gS=B(_gH(_gK,_));return [1,_17,_gS];}else{var _gT=B(_gH(_gK,_)),_gU=new T(function(){return E(B(_fV((_gR+2|0)+1|0,(_gQ-2|0)-1|0,_gP))[1]);});return [1,[1,[0,_gM,[0,_gN[1],_gU]],[1,[0,[0,_gM[1],_gU],_gN],_17]],_gT];}}},_gV=B(_gH(_gj,_)),_gW=new T(function(){return E(B(_fV((_gr+2|0)+1|0,(_gq-2|0)-1|0,_gp))[1]);});return [1,[1,[0,_gl,[0,_gm[1],_gW]],[1,[0,[0,_gl[1],_gW],_gm],_17]],_gV];}}}})(_gd,_);if(_ge!=null){return _ge;}}},_gX=function(_gY,_){var _gZ=E(_gY);if(!_gZ[0]){return _17;}else{var _h0=_gZ[2],_h1=E(_gZ[1]),_h2=E(_h1[1]),_h3=E(_h1[2]),_h4=E(_gb),_h5=_h4(),_h6=_h5,_h7=E(_h3[1]),_h8=E(_h2[1]);if((_h7-_h8|0)<4){var _h9=function(_ha,_){var _hb=E(_ha);if(!_hb[0]){return _17;}else{var _hc=_hb[2],_hd=E(_hb[1]),_he=E(_hd[1]),_hf=E(_hd[2]),_hg=_h4(),_hh=_hg,_hi=E(_hf[1]),_hj=E(_he[1]);if((_hi-_hj|0)<4){var _hk=B(_h9(_hc,_));return [1,_17,_hk];}else{var _hl=B(_h9(_hc,_)),_hm=new T(function(){return E(B(_fV((_hj+2|0)+1|0,(_hi-2|0)-1|0,_hh))[1]);});return [1,[1,[0,_he,[0,_hm,_hf[2]]],[1,[0,[0,_hm,_he[2]],_hf],_17]],_hl];}}},_hn=B(_h9(_h0,_));return [1,_17,_hn];}else{var _ho=function(_hp,_){var _hq=E(_hp);if(!_hq[0]){return _17;}else{var _hr=_hq[2],_hs=E(_hq[1]),_ht=E(_hs[1]),_hu=E(_hs[2]),_hv=_h4(),_hw=_hv,_hx=E(_hu[1]),_hy=E(_ht[1]);if((_hx-_hy|0)<4){var _hz=B(_ho(_hr,_));return [1,_17,_hz];}else{var _hA=B(_ho(_hr,_)),_hB=new T(function(){return E(B(_fV((_hy+2|0)+1|0,(_hx-2|0)-1|0,_hw))[1]);});return [1,[1,[0,_ht,[0,_hB,_hu[2]]],[1,[0,[0,_hB,_ht[2]],_hu],_17]],_hA];}}},_hC=B(_ho(_h0,_)),_hD=new T(function(){return E(B(_fV((_h8+2|0)+1|0,(_h7-2|0)-1|0,_h6))[1]);});return [1,[1,[0,_h2,[0,_hD,_h3[2]]],[1,[0,[0,_hD,_h2[2]],_h3],_17]],_hC];}}},_hE=0,_hF=[0,_hE,_hE],_hG=24,_hH=74,_hI=[0,_hH,_hG],_hJ=[0,_hF,_hI],_hK=[1,_hJ,_17],_hL=function(_hM,_){var _hN=E(_hM);if(_hN==1){var _hO=B(_gX(_hK,_)),_hP=B(_gc(_hO,_)),_hQ=_hP;return new T(function(){return B(_f1(_hQ));});}else{var _hR=B(_hL(_hN+1|0,_)),_hS=B(_gX(_hR,_)),_hT=B(_gc(_hS,_)),_hU=_hT;return new T(function(){return B(_f1(_hU));});}},_hV=function(_hW,_){var _hX=E(_hW);if(!_hX[0]){return _17;}else{var _hY=_hX[2],_hZ=E(_hX[1]),_i0=E(_hZ[1]),_i1=E(_hZ[2]),_i2=E(_gb),_i3=_i2(),_i4=_i3,_i5=_i2(),_i6=_i5,_i7=_i2(),_i8=_i7,_i9=_i2(),_ia=_i9,_ib=E(_i0[1]),_ic=E(_i1[1]);if((_ib+1|0)>(_ic-2|0)){var _id=function(_ie,_){while(1){var _if=(function(_ig,_){var _ih=E(_ig);if(!_ih[0]){return _17;}else{var _ii=_ih[2],_ij=E(_ih[1]),_ik=E(_ij[1]),_il=E(_ij[2]),_im=_i2(),_in=_im,_io=_i2(),_ip=_io,_iq=_i2(),_ir=_iq,_is=_i2(),_it=_is,_iu=E(_ik[1]),_iv=E(_il[1]);if((_iu+1|0)>(_iv-2|0)){_ie=_ii;return null;}else{var _iw=E(_ik[2]),_ix=E(_il[2]);if((_iw+1|0)>(_ix-2|0)){_ie=_ii;return null;}else{var _iy=B(_id(_ii,_)),_iz=new T(function(){return E(B(_fV(_iu+1|0,_iv-2|0,_in))[1]);}),_iA=new T(function(){return E(B(_fV(_iw+1|0,_ix-2|0,_ir))[1]);}),_iB=new T(function(){return E(B(_fV((E(_iA)+2|0)-1|0,_ix-1|0,_it))[1]);}),_iC=new T(function(){return E(B(_fV((E(_iz)+2|0)-1|0,_iv-1|0,_ip))[1]);});return [1,[0,[0,_iz,_iA],[0,_iC,_iB]],_iy];}}}})(_ie,_);if(_if!=null){return _if;}}};return new F(function(){return _id(_hY,_);});}else{var _iD=E(_i0[2]),_iE=E(_i1[2]);if((_iD+1|0)>(_iE-2|0)){var _iF=function(_iG,_){while(1){var _iH=(function(_iI,_){var _iJ=E(_iI);if(!_iJ[0]){return _17;}else{var _iK=_iJ[2],_iL=E(_iJ[1]),_iM=E(_iL[1]),_iN=E(_iL[2]),_iO=_i2(),_iP=_iO,_iQ=_i2(),_iR=_iQ,_iS=_i2(),_iT=_iS,_iU=_i2(),_iV=_iU,_iW=E(_iM[1]),_iX=E(_iN[1]);if((_iW+1|0)>(_iX-2|0)){_iG=_iK;return null;}else{var _iY=E(_iM[2]),_iZ=E(_iN[2]);if((_iY+1|0)>(_iZ-2|0)){_iG=_iK;return null;}else{var _j0=B(_iF(_iK,_)),_j1=new T(function(){return E(B(_fV(_iW+1|0,_iX-2|0,_iP))[1]);}),_j2=new T(function(){return E(B(_fV(_iY+1|0,_iZ-2|0,_iT))[1]);}),_j3=new T(function(){return E(B(_fV((E(_j2)+2|0)-1|0,_iZ-1|0,_iV))[1]);}),_j4=new T(function(){return E(B(_fV((E(_j1)+2|0)-1|0,_iX-1|0,_iR))[1]);});return [1,[0,[0,_j1,_j2],[0,_j4,_j3]],_j0];}}}})(_iG,_);if(_iH!=null){return _iH;}}};return new F(function(){return _iF(_hY,_);});}else{var _j5=function(_j6,_){while(1){var _j7=(function(_j8,_){var _j9=E(_j8);if(!_j9[0]){return _17;}else{var _ja=_j9[2],_jb=E(_j9[1]),_jc=E(_jb[1]),_jd=E(_jb[2]),_je=_i2(),_jf=_je,_jg=_i2(),_jh=_jg,_ji=_i2(),_jj=_ji,_jk=_i2(),_jl=_jk,_jm=E(_jc[1]),_jn=E(_jd[1]);if((_jm+1|0)>(_jn-2|0)){_j6=_ja;return null;}else{var _jo=E(_jc[2]),_jp=E(_jd[2]);if((_jo+1|0)>(_jp-2|0)){_j6=_ja;return null;}else{var _jq=B(_j5(_ja,_)),_jr=new T(function(){return E(B(_fV(_jm+1|0,_jn-2|0,_jf))[1]);}),_js=new T(function(){return E(B(_fV(_jo+1|0,_jp-2|0,_jj))[1]);}),_jt=new T(function(){return E(B(_fV((E(_js)+2|0)-1|0,_jp-1|0,_jl))[1]);}),_ju=new T(function(){return E(B(_fV((E(_jr)+2|0)-1|0,_jn-1|0,_jh))[1]);});return [1,[0,[0,_jr,_js],[0,_ju,_jt]],_jq];}}}})(_j6,_);if(_j7!=null){return _j7;}}},_jv=B(_j5(_hY,_)),_jw=new T(function(){return E(B(_fV(_ib+1|0,_ic-2|0,_i4))[1]);}),_jx=new T(function(){return E(B(_fV(_iD+1|0,_iE-2|0,_i8))[1]);}),_jy=new T(function(){return E(B(_fV((E(_jx)+2|0)-1|0,_iE-1|0,_ia))[1]);}),_jz=new T(function(){return E(B(_fV((E(_jw)+2|0)-1|0,_ic-1|0,_i6))[1]);});return [1,[0,[0,_jw,_jx],[0,_jz,_jy]],_jv];}}}},_jA=function(_jB,_jC,_){var _jD=E(_jB);if(!_jD[0]){return _17;}else{var _jE=_jD[2],_jF=E(_jC);if(!_jF[0]){return _17;}else{var _jG=_jF[2],_jH=E(_jD[1]),_jI=E(_jH[2]),_jJ=E(_jF[1]),_jK=E(_jJ[1]),_jL=_jK[1],_jM=E(_jJ[2])[1],_jN=E(E(_jH[1])[2]);if(!E(_jN)){var _jO=B(_jA(_jE,_jG,_));return [1,_17,_jO];}else{var _jP=E(_gb),_jQ=_jP(),_jR=_jQ,_jS=function(_jT,_jU,_){var _jV=E(_jT);if(!_jV[0]){return _17;}else{var _jW=_jV[2],_jX=E(_jU);if(!_jX[0]){return _17;}else{var _jY=_jX[2],_jZ=E(_jV[1]),_k0=E(_jZ[2]),_k1=E(_jX[1]),_k2=E(_k1[1]),_k3=_k2[1],_k4=E(_k1[2])[1],_k5=E(E(_jZ[1])[2]);if(!E(_k5)){var _k6=B(_jS(_jW,_jY,_));return [1,_17,_k6];}else{var _k7=_jP(),_k8=_k7,_k9=B(_jS(_jW,_jY,_)),_ka=new T(function(){return E(B(_fV(E(_k3),E(_k4),_k8))[1]);});return [1,[1,[0,[0,[0,_ka,_k5],[0,_ka,_k2[2]]],[0,_ka,_k5]],_17],_k9];}}}},_kb=B(_jS(_jE,_jG,_)),_kc=new T(function(){return E(B(_fV(E(_jL),E(_jM),_jR))[1]);});return [1,[1,[0,[0,[0,_kc,_jN],[0,_kc,_jK[2]]],[0,_kc,_jN]],_17],_kb];}}}},_kd=function(_ke,_kf,_){var _kg=E(_ke);if(!_kg[0]){return _17;}else{var _kh=_kg[2],_ki=E(_kf);if(!_ki[0]){return _17;}else{var _kj=_ki[2],_kk=E(_kg[1]),_kl=E(_kk[1]),_km=E(_ki[1]),_kn=E(_km[1])[1],_ko=E(_km[2]),_kp=_ko[1],_kq=E(E(_kk[2])[2]);if(E(_kq)==24){var _kr=B(_kd(_kh,_kj,_));return [1,_17,_kr];}else{var _ks=E(_gb),_kt=_ks(),_ku=_kt,_kv=function(_kw,_kx,_){var _ky=E(_kw);if(!_ky[0]){return _17;}else{var _kz=_ky[2],_kA=E(_kx);if(!_kA[0]){return _17;}else{var _kB=_kA[2],_kC=E(_ky[1]),_kD=E(_kC[1]),_kE=E(_kA[1]),_kF=E(_kE[1])[1],_kG=E(_kE[2]),_kH=_kG[1],_kI=E(E(_kC[2])[2]);if(E(_kI)==24){var _kJ=B(_kv(_kz,_kB,_));return [1,_17,_kJ];}else{var _kK=_ks(),_kL=_kK,_kM=B(_kv(_kz,_kB,_)),_kN=new T(function(){return E(B(_fV(E(_kF),E(_kH),_kL))[1]);});return [1,[1,[0,[0,[0,_kN,_kG[2]],[0,_kN,_kI]],[0,_kN,_kI]],_17],_kM];}}}},_kO=B(_kv(_kh,_kj,_)),_kP=new T(function(){return E(B(_fV(E(_kn),E(_kp),_ku))[1]);});return [1,[1,[0,[0,[0,_kP,_ko[2]],[0,_kP,_kq]],[0,_kP,_kq]],_17],_kO];}}}},_kQ=function(_kR,_kS,_){var _kT=E(_kR);if(!_kT[0]){return _17;}else{var _kU=_kT[2],_kV=E(_kS);if(!_kV[0]){return _17;}else{var _kW=_kV[2],_kX=E(_kT[1]),_kY=E(_kX[2]),_kZ=E(_kV[1]),_l0=E(_kZ[1]),_l1=_l0[2],_l2=E(_kZ[2])[2],_l3=E(E(_kX[1])[1]);if(!E(_l3)){var _l4=B(_kQ(_kU,_kW,_));return [1,_17,_l4];}else{var _l5=E(_gb),_l6=_l5(),_l7=_l6,_l8=function(_l9,_la,_){var _lb=E(_l9);if(!_lb[0]){return _17;}else{var _lc=_lb[2],_ld=E(_la);if(!_ld[0]){return _17;}else{var _le=_ld[2],_lf=E(_lb[1]),_lg=E(_lf[2]),_lh=E(_ld[1]),_li=E(_lh[1]),_lj=_li[2],_lk=E(_lh[2])[2],_ll=E(E(_lf[1])[1]);if(!E(_ll)){var _lm=B(_l8(_lc,_le,_));return [1,_17,_lm];}else{var _ln=_l5(),_lo=_ln,_lp=B(_l8(_lc,_le,_)),_lq=new T(function(){return E(B(_fV(E(_lj),E(_lk),_lo))[1]);});return [1,[1,[0,[0,[0,_ll,_lq],[0,_li[1],_lq]],[0,_ll,_lq]],_17],_lp];}}}},_lr=B(_l8(_kU,_kW,_)),_ls=new T(function(){return E(B(_fV(E(_l1),E(_l2),_l7))[1]);});return [1,[1,[0,[0,[0,_l3,_ls],[0,_l0[1],_ls]],[0,_l3,_ls]],_17],_lr];}}}},_lt=function(_lu,_lv,_){var _lw=E(_lu);if(!_lw[0]){return _17;}else{var _lx=_lw[2],_ly=E(_lv);if(!_ly[0]){return _17;}else{var _lz=_ly[2],_lA=E(_lw[1]),_lB=E(_lA[1]),_lC=E(_ly[1]),_lD=E(_lC[1])[2],_lE=E(_lC[2]),_lF=_lE[2],_lG=E(E(_lA[2])[1]);if(E(_lG)==74){var _lH=B(_lt(_lx,_lz,_));return [1,_17,_lH];}else{var _lI=E(_gb),_lJ=_lI(),_lK=_lJ,_lL=function(_lM,_lN,_){var _lO=E(_lM);if(!_lO[0]){return _17;}else{var _lP=_lO[2],_lQ=E(_lN);if(!_lQ[0]){return _17;}else{var _lR=_lQ[2],_lS=E(_lO[1]),_lT=E(_lS[1]),_lU=E(_lQ[1]),_lV=E(_lU[1])[2],_lW=E(_lU[2]),_lX=_lW[2],_lY=E(E(_lS[2])[1]);if(E(_lY)==74){var _lZ=B(_lL(_lP,_lR,_));return [1,_17,_lZ];}else{var _m0=_lI(),_m1=_m0,_m2=B(_lL(_lP,_lR,_)),_m3=new T(function(){return E(B(_fV(E(_lV),E(_lX),_m1))[1]);});return [1,[1,[0,[0,[0,_lW[1],_m3],[0,_lY,_m3]],[0,_lY,_m3]],_17],_m2];}}}},_m4=B(_lL(_lx,_lz,_)),_m5=new T(function(){return E(B(_fV(E(_lD),E(_lF),_lK))[1]);});return [1,[1,[0,[0,[0,_lE[1],_m5],[0,_lG,_m5]],[0,_lG,_m5]],_17],_m4];}}}},_m6=function(_m7,_m8){return [0,1,E(_m7),_m8,E(_8w),E(_8w)];},_m9=function(_ma,_mb,_mc){var _md=E(_mc);if(!_md[0]){return new F(function(){return _9k(_md[2],_md[3],_md[4],B(_m9(_ma,_mb,_md[5])));});}else{return new F(function(){return _m6(_ma,_mb);});}},_me=function(_mf,_mg,_mh){var _mi=E(_mh);if(!_mi[0]){return new F(function(){return _8B(_mi[2],_mi[3],B(_me(_mf,_mg,_mi[4])),_mi[5]);});}else{return new F(function(){return _m6(_mf,_mg);});}},_mj=function(_mk,_ml,_mm,_mn,_mo,_mp,_mq){return new F(function(){return _8B(_mn,_mo,B(_me(_mk,_ml,_mp)),_mq);});},_mr=function(_ms,_mt,_mu,_mv,_mw,_mx,_my,_mz){var _mA=E(_mu);if(!_mA[0]){var _mB=_mA[1],_mC=_mA[2],_mD=_mA[3],_mE=_mA[4],_mF=_mA[5];if((imul(3,_mB)|0)>=_mv){if((imul(3,_mv)|0)>=_mB){return [0,(_mB+_mv|0)+1|0,E(_ms),_mt,E(_mA),[0,_mv,E(_mw),_mx,E(_my),E(_mz)]];}else{return new F(function(){return _9k(_mC,_mD,_mE,B(_mr(_ms,_mt,_mF,_mv,_mw,_mx,_my,_mz)));});}}else{return new F(function(){return _8B(_mw,_mx,B(_mG(_ms,_mt,_mB,_mC,_mD,_mE,_mF,_my)),_mz);});}}else{return new F(function(){return _mj(_ms,_mt,_mv,_mw,_mx,_my,_mz);});}},_mG=function(_mH,_mI,_mJ,_mK,_mL,_mM,_mN,_mO){var _mP=E(_mO);if(!_mP[0]){var _mQ=_mP[1],_mR=_mP[2],_mS=_mP[3],_mT=_mP[4],_mU=_mP[5];if((imul(3,_mJ)|0)>=_mQ){if((imul(3,_mQ)|0)>=_mJ){return [0,(_mJ+_mQ|0)+1|0,E(_mH),_mI,[0,_mJ,E(_mK),_mL,E(_mM),E(_mN)],E(_mP)];}else{return new F(function(){return _9k(_mK,_mL,_mM,B(_mr(_mH,_mI,_mN,_mQ,_mR,_mS,_mT,_mU)));});}}else{return new F(function(){return _8B(_mR,_mS,B(_mG(_mH,_mI,_mJ,_mK,_mL,_mM,_mN,_mT)),_mU);});}}else{return new F(function(){return _m9(_mH,_mI,[0,_mJ,E(_mK),_mL,E(_mM),E(_mN)]);});}},_mV=function(_mW,_mX,_mY,_mZ){var _n0=E(_mY);if(!_n0[0]){var _n1=_n0[1],_n2=_n0[2],_n3=_n0[3],_n4=_n0[4],_n5=_n0[5],_n6=E(_mZ);if(!_n6[0]){var _n7=_n6[1],_n8=_n6[2],_n9=_n6[3],_na=_n6[4],_nb=_n6[5];if((imul(3,_n1)|0)>=_n7){if((imul(3,_n7)|0)>=_n1){return [0,(_n1+_n7|0)+1|0,E(_mW),_mX,E(_n0),E(_n6)];}else{return new F(function(){return _9k(_n2,_n3,_n4,B(_mr(_mW,_mX,_n5,_n7,_n8,_n9,_na,_nb)));});}}else{return new F(function(){return _8B(_n8,_n9,B(_mG(_mW,_mX,_n1,_n2,_n3,_n4,_n5,_na)),_nb);});}}else{return new F(function(){return _m9(_mW,_mX,_n0);});}}else{return new F(function(){return _me(_mW,_mX,_mZ);});}},_nc=function(_nd,_ne,_nf,_ng,_nh){var _ni=E(_nd);if(_ni==1){var _nj=E(_nh);if(!_nj[0]){return [0,[0,1,[0,_ne,_nf],_ng,E(_8w),E(_8w)],_17,_17];}else{var _nk=E(E(_nj[1])[1]),_nl=E(_nk[1]);return (_ne>=_nl)?(_ne!=_nl)?[0,[0,1,[0,_ne,_nf],_ng,E(_8w),E(_8w)],_17,_nj]:(_nf<E(_nk[2]))?[0,[0,1,[0,_ne,_nf],_ng,E(_8w),E(_8w)],_nj,_17]:[0,[0,1,[0,_ne,_nf],_ng,E(_8w),E(_8w)],_17,_nj]:[0,[0,1,[0,_ne,_nf],_ng,E(_8w),E(_8w)],_nj,_17];}}else{var _nm=B(_nc(_ni>>1,_ne,_nf,_ng,_nh)),_nn=_nm[1],_no=_nm[3],_np=E(_nm[2]);if(!_np[0]){return [0,_nn,_17,_no];}else{var _nq=E(_np[1]),_nr=_nq[1],_ns=_nq[2],_nt=E(_np[2]);if(!_nt[0]){var _nu=new T(function(){return B(_m9(_nr,_ns,_nn));});return [0,_nu,_17,_no];}else{var _nv=_nt[2],_nw=E(_nt[1]),_nx=_nw[2],_ny=E(_nr),_nz=E(_nw[1]),_nA=_nz[2],_nB=E(_ny[1]),_nC=E(_nz[1]);if(_nB>=_nC){if(_nB!=_nC){return [0,_nn,_17,_np];}else{var _nD=E(_nA);if(E(_ny[2])<_nD){var _nE=B(_nc(_ni>>1,_nC,_nD,_nx,_nv)),_nF=_nE[1],_nG=new T(function(){return B(_mV(_ny,_ns,_nn,_nF));});return [0,_nG,_nE[2],_nE[3]];}else{return [0,_nn,_17,_np];}}}else{var _nH=B(_nI(_ni>>1,_nC,_nA,_nx,_nv)),_nJ=_nH[1],_nK=new T(function(){return B(_mV(_ny,_ns,_nn,_nJ));});return [0,_nK,_nH[2],_nH[3]];}}}}},_nI=function(_nL,_nM,_nN,_nO,_nP){var _nQ=E(_nL);if(_nQ==1){var _nR=E(_nP);if(!_nR[0]){return [0,[0,1,[0,_nM,_nN],_nO,E(_8w),E(_8w)],_17,_17];}else{var _nS=E(E(_nR[1])[1]),_nT=E(_nS[1]);if(_nM>=_nT){if(_nM!=_nT){return [0,[0,1,[0,_nM,_nN],_nO,E(_8w),E(_8w)],_17,_nR];}else{var _nU=E(_nN);return (_nU<E(_nS[2]))?[0,[0,1,[0,_nM,_nU],_nO,E(_8w),E(_8w)],_nR,_17]:[0,[0,1,[0,_nM,_nU],_nO,E(_8w),E(_8w)],_17,_nR];}}else{return [0,[0,1,[0,_nM,_nN],_nO,E(_8w),E(_8w)],_nR,_17];}}}else{var _nV=B(_nI(_nQ>>1,_nM,_nN,_nO,_nP)),_nW=_nV[1],_nX=_nV[3],_nY=E(_nV[2]);if(!_nY[0]){return [0,_nW,_17,_nX];}else{var _nZ=E(_nY[1]),_o0=_nZ[1],_o1=_nZ[2],_o2=E(_nY[2]);if(!_o2[0]){var _o3=new T(function(){return B(_m9(_o0,_o1,_nW));});return [0,_o3,_17,_nX];}else{var _o4=_o2[2],_o5=E(_o2[1]),_o6=_o5[2],_o7=E(_o0),_o8=E(_o5[1]),_o9=_o8[2],_oa=E(_o7[1]),_ob=E(_o8[1]);if(_oa>=_ob){if(_oa!=_ob){return [0,_nW,_17,_nY];}else{var _oc=E(_o9);if(E(_o7[2])<_oc){var _od=B(_nc(_nQ>>1,_ob,_oc,_o6,_o4)),_oe=_od[1],_of=new T(function(){return B(_mV(_o7,_o1,_nW,_oe));});return [0,_of,_od[2],_od[3]];}else{return [0,_nW,_17,_nY];}}}else{var _og=B(_nI(_nQ>>1,_ob,_o9,_o6,_o4)),_oh=_og[1],_oi=new T(function(){return B(_mV(_o7,_o1,_nW,_oh));});return [0,_oi,_og[2],_og[3]];}}}}},_oj=function(_ok,_ol){while(1){var _om=E(_ol);if(!_om[0]){return E(_ok);}else{var _on=E(_om[1]),_oo=E(_on[1]),_op=B(_eI(_oo[1],_oo[2],_on[2],_ok));_ol=_om[2];_ok=_op;continue;}}},_oq=function(_or,_os,_ot,_ou,_ov){return new F(function(){return _oj(B(_eI(_os,_ot,_ou,_or)),_ov);});},_ow=function(_ox,_oy,_oz){var _oA=E(_oy),_oB=E(_oA[1]);return new F(function(){return _oj(B(_eI(_oB[1],_oB[2],_oA[2],_ox)),_oz);});},_oC=function(_oD,_oE,_oF){var _oG=E(_oF);if(!_oG[0]){return E(_oE);}else{var _oH=E(_oG[1]),_oI=_oH[1],_oJ=_oH[2],_oK=E(_oG[2]);if(!_oK[0]){return new F(function(){return _m9(_oI,_oJ,_oE);});}else{var _oL=_oK[2],_oM=E(_oK[1]),_oN=_oM[2],_oO=E(_oI),_oP=_oO[2],_oQ=E(_oM[1]),_oR=_oQ[2],_oS=E(_oO[1]),_oT=E(_oQ[1]),_oU=function(_oV){var _oW=B(_nI(_oD,_oT,_oR,_oN,_oL)),_oX=_oW[1],_oY=E(_oW[3]);if(!_oY[0]){return new F(function(){return _oC(_oD<<1,B(_mV(_oO,_oJ,_oE,_oX)),_oW[2]);});}else{return new F(function(){return _ow(B(_mV(_oO,_oJ,_oE,_oX)),_oY[1],_oY[2]);});}};if(_oS>=_oT){if(_oS!=_oT){return new F(function(){return _oq(_oE,_oS,_oP,_oJ,_oK);});}else{var _oZ=E(_oP);if(_oZ<E(_oR)){return new F(function(){return _oU(_);});}else{return new F(function(){return _oq(_oE,_oS,_oZ,_oJ,_oK);});}}}else{return new F(function(){return _oU(_);});}}}},_p0=function(_p1,_p2,_p3,_p4,_p5,_p6){var _p7=E(_p6);if(!_p7[0]){return new F(function(){return _m9([0,_p3,_p4],_p5,_p2);});}else{var _p8=_p7[2],_p9=E(_p7[1]),_pa=_p9[2],_pb=E(_p9[1]),_pc=_pb[2],_pd=E(_pb[1]),_pe=function(_pf){var _pg=B(_nI(_p1,_pd,_pc,_pa,_p8)),_ph=_pg[1],_pi=E(_pg[3]);if(!_pi[0]){return new F(function(){return _oC(_p1<<1,B(_mV([0,_p3,_p4],_p5,_p2,_ph)),_pg[2]);});}else{return new F(function(){return _ow(B(_mV([0,_p3,_p4],_p5,_p2,_ph)),_pi[1],_pi[2]);});}};if(_p3>=_pd){if(_p3!=_pd){return new F(function(){return _oq(_p2,_p3,_p4,_p5,_p7);});}else{if(_p4<E(_pc)){return new F(function(){return _pe(_);});}else{return new F(function(){return _oq(_p2,_p3,_p4,_p5,_p7);});}}}else{return new F(function(){return _pe(_);});}}},_pj=function(_pk,_pl,_pm,_pn,_po,_pp){var _pq=E(_pp);if(!_pq[0]){return new F(function(){return _m9([0,_pm,_pn],_po,_pl);});}else{var _pr=_pq[2],_ps=E(_pq[1]),_pt=_ps[2],_pu=E(_ps[1]),_pv=_pu[2],_pw=E(_pu[1]),_px=function(_py){var _pz=B(_nI(_pk,_pw,_pv,_pt,_pr)),_pA=_pz[1],_pB=E(_pz[3]);if(!_pB[0]){return new F(function(){return _oC(_pk<<1,B(_mV([0,_pm,_pn],_po,_pl,_pA)),_pz[2]);});}else{return new F(function(){return _ow(B(_mV([0,_pm,_pn],_po,_pl,_pA)),_pB[1],_pB[2]);});}};if(_pm>=_pw){if(_pm!=_pw){return new F(function(){return _oq(_pl,_pm,_pn,_po,_pq);});}else{var _pC=E(_pn);if(_pC<E(_pv)){return new F(function(){return _px(_);});}else{return new F(function(){return _oq(_pl,_pm,_pC,_po,_pq);});}}}else{return new F(function(){return _px(_);});}}},_pD=function(_pE){var _pF=E(_pE);if(!_pF[0]){return [1];}else{var _pG=E(_pF[1]),_pH=_pG[1],_pI=_pG[2],_pJ=E(_pF[2]);if(!_pJ[0]){return [0,1,E(_pH),_pI,E(_8w),E(_8w)];}else{var _pK=_pJ[2],_pL=E(_pJ[1]),_pM=_pL[2],_pN=E(_pH),_pO=E(_pL[1]),_pP=_pO[2],_pQ=E(_pN[1]),_pR=E(_pO[1]);if(_pQ>=_pR){if(_pQ!=_pR){return new F(function(){return _oq([0,1,E(_pN),_pI,E(_8w),E(_8w)],_pR,_pP,_pM,_pK);});}else{var _pS=E(_pP);if(E(_pN[2])<_pS){return new F(function(){return _p0(1,[0,1,E(_pN),_pI,E(_8w),E(_8w)],_pR,_pS,_pM,_pK);});}else{return new F(function(){return _oq([0,1,E(_pN),_pI,E(_8w),E(_8w)],_pR,_pS,_pM,_pK);});}}}else{return new F(function(){return _pj(1,[0,1,E(_pN),_pI,E(_8w),E(_8w)],_pR,_pP,_pM,_pK);});}}}},_pT=new T(function(){return B(_7H(0,24));}),_pU=function(_pV){var _pW=_pV,_pX=new T(function(){var _pY=E(_pV);if(_pY==74){return [0];}else{return B(_pU(_pY+1|0));}}),_pZ=function(_q0){var _q1=E(_q0);if(!_q1[0]){return E(_pX);}else{var _q2=_q1[2],_q3=new T(function(){return B(_pZ(_q2));});return [1,[0,_pW,_q1[1]],_q3];}};return new F(function(){return _pZ(_pT);});},_q4=new T(function(){return B(_pU(0));}),_q5=32,_q6=new T(function(){return [1,_q5,_q6];}),_q7=function(_q8,_q9){var _qa=E(_q8);if(!_qa[0]){return [0];}else{var _qb=_qa[2],_qc=E(_q9);if(!_qc[0]){return [0];}else{var _qd=_qc[2],_qe=new T(function(){return B(_q7(_qb,_qd));});return [1,[0,_qa[1],_qc[1]],_qe];}}},_qf=new T(function(){return B(_q7(_q4,_q6));}),_qg=new T(function(){return B(_pD(_qf));}),_qh=35,_qi=function(_qj){return E(E(_qj)[1]);},_qk=function(_ql,_qm,_qn){while(1){var _qo=E(_qn);if(!_qo[0]){return false;}else{if(!B(A(_qi,[_ql,_qm,_qo[1]]))){_qn=_qo[2];continue;}else{return true;}}}},_qp=function(_qq){return E(E(_qq)[1]);},_qr=function(_qs){var _qt=E(_qs);if(!_qt[0]){return [0];}else{var _qu=_qt[2],_qv=new T(function(){return B(_qr(_qu));},1);return new F(function(){return _1t(_qt[1],_qv);});}},_qw=new T(function(){return B(unCStr("Control.Exception.Base"));}),_qx=new T(function(){return B(unCStr("base"));}),_qy=new T(function(){return B(unCStr("PatternMatchFail"));}),_qz=new T(function(){var _qA=hs_wordToWord64(18445595),_qB=hs_wordToWord64(52003073);return [0,_qA,_qB,[0,_qA,_qB,_qx,_qw,_qy],_17,_17];}),_qC=function(_qD){return E(_qz);},_qE=function(_qF){var _qG=E(_qF);return new F(function(){return _1f(B(_1d(_qG[1])),_qC,_qG[2]);});},_qH=function(_qI){return E(E(_qI)[1]);},_qJ=function(_qK){return [0,_qL,_qK];},_qM=function(_qN,_qO){return new F(function(){return _1t(E(_qN)[1],_qO);});},_qP=function(_qQ,_qR){return new F(function(){return _2D(_qM,_qQ,_qR);});},_qS=function(_qT,_qU,_qV){return new F(function(){return _1t(E(_qU)[1],_qV);});},_qW=[0,_qS,_qH,_qP],_qL=new T(function(){return [0,_qC,_qW,_qJ,_qE,_qH];}),_qX=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_qY=function(_qZ){return E(E(_qZ)[3]);},_r0=function(_r1,_r2){var _r3=new T(function(){return B(A(_qY,[_r2,_r1]));});return new F(function(){return die(_r3);});},_r4=function(_r5,_fC){return new F(function(){return _r0(_r5,_fC);});},_r6=function(_r7,_r8){var _r9=E(_r8);if(!_r9[0]){return [0,_17,_17];}else{var _ra=_r9[1],_rb=_r9[2];if(!B(A(_r7,[_ra]))){return [0,_17,_r9];}else{var _rc=new T(function(){var _rd=B(_r6(_r7,_rb));return [0,_rd[1],_rd[2]];}),_re=new T(function(){return E(E(_rc)[2]);}),_rf=new T(function(){return E(E(_rc)[1]);});return [0,[1,_ra,_rf],_re];}}},_rg=32,_rh=new T(function(){return B(unCStr("\n"));}),_ri=function(_rj){return (E(_rj)==124)?false:true;},_rk=function(_rl,_rm){var _rn=B(_r6(_ri,B(unCStr(_rl)))),_ro=_rn[1],_rp=function(_rq,_rr){var _rs=new T(function(){var _rt=new T(function(){var _ru=new T(function(){return B(_1t(_rr,_rh));},1);return B(_1t(_rm,_ru));});return B(unAppCStr(": ",_rt));},1);return new F(function(){return _1t(_rq,_rs);});},_rv=E(_rn[2]);if(!_rv[0]){return new F(function(){return _rp(_ro,_17);});}else{if(E(_rv[1])==124){return new F(function(){return _rp(_ro,[1,_rg,_rv[2]]);});}else{return new F(function(){return _rp(_ro,_17);});}}},_rw=function(_rx){var _ry=new T(function(){return B(_rk(_rx,_qX));});return new F(function(){return _r4([0,_ry],_qL);});},_rz=function(_rA){return new F(function(){return _rw("Dungeon.hs:(127,5)-(128,21)|function tup");});},_rB=new T(function(){return B(_rz(_));}),_rC=function(_rD){var _rE=E(_rD);if(!_rE[0]){return E(_rB);}else{var _rF=_rE[1],_rG=E(_rE[2]);return (_rG[0]==0)?[0,_rF,_rF]:(E(_rG[2])[0]==0)?[0,_rF,_rG[1]]:E(_rB);}},_rH=function(_rI,_rJ){return new F(function(){return _3W(E(E(_rI)[2]),E(E(_rJ)[2]));});},_rK=[1,_17,_17],_rL=function(_rM,_rN){var _rO=function(_rP,_rQ){var _rR=E(_rP);if(!_rR[0]){return E(_rQ);}else{var _rS=_rR[1],_rT=_rR[2],_rU=E(_rQ);if(!_rU[0]){return E(_rR);}else{var _rV=_rU[1],_rW=_rU[2];if(B(A(_rM,[_rS,_rV]))==2){var _rX=new T(function(){return B(_rO(_rR,_rW));});return [1,_rV,_rX];}else{var _rY=new T(function(){return B(_rO(_rT,_rU));});return [1,_rS,_rY];}}}},_rZ=function(_s0){var _s1=E(_s0);if(!_s1[0]){return [0];}else{var _s2=_s1[1],_s3=E(_s1[2]);if(!_s3[0]){return E(_s1);}else{var _s4=_s3[1],_s5=_s3[2],_s6=new T(function(){return B(_rZ(_s5));}),_s7=new T(function(){return B(_rO(_s2,_s4));});return [1,_s7,_s6];}}},_s8=new T(function(){return B(_s9(B(_rZ(_17))));}),_s9=function(_sa){while(1){var _sb=E(_sa);if(!_sb[0]){return E(_s8);}else{if(!E(_sb[2])[0]){return E(_sb[1]);}else{_sa=B(_rZ(_sb));continue;}}}},_sc=new T(function(){return B(_sd(_17));}),_se=function(_sf,_sg,_sh){while(1){var _si=(function(_sj,_sk,_sl){var _sm=E(_sl);if(!_sm[0]){return [1,[1,_sj,_sk],_sc];}else{var _sn=_sm[1];if(B(A(_rM,[_sj,_sn]))==2){_sf=_sn;var _so=[1,_sj,_sk];_sh=_sm[2];_sg=_so;return null;}else{var _sp=new T(function(){return B(_sd(_sm));});return [1,[1,_sj,_sk],_sp];}}})(_sf,_sg,_sh);if(_si!=null){return _si;}}},_sq=function(_sr,_ss,_st){while(1){var _su=(function(_sv,_sw,_sx){var _sy=E(_sx);if(!_sy[0]){var _sz=new T(function(){return B(A(_sw,[[1,_sv,_17]]));});return [1,_sz,_sc];}else{var _sA=_sy[1],_sB=_sy[2];switch(B(A(_rM,[_sv,_sA]))){case 0:var _sC=function(_sD){return new F(function(){return A(_sw,[[1,_sv,_sD]]);});};_sr=_sA;_ss=_sC;_st=_sB;return null;case 1:var _sE=function(_sF){return new F(function(){return A(_sw,[[1,_sv,_sF]]);});};_sr=_sA;_ss=_sE;_st=_sB;return null;default:var _sG=new T(function(){return B(_sd(_sy));}),_sH=new T(function(){return B(A(_sw,[[1,_sv,_17]]));});return [1,_sH,_sG];}}})(_sr,_ss,_st);if(_su!=null){return _su;}}},_sd=function(_sI){var _sJ=E(_sI);if(!_sJ[0]){return E(_rK);}else{var _sK=_sJ[1],_sL=E(_sJ[2]);if(!_sL[0]){return [1,_sJ,_17];}else{var _sM=_sL[1],_sN=_sL[2];if(B(A(_rM,[_sK,_sM]))==2){return new F(function(){return _se(_sM,[1,_sK,_17],_sN);});}else{var _sO=function(_sP){return [1,_sK,_sP];};return new F(function(){return _sq(_sM,_sO,_sN);});}}}};return new F(function(){return _s9(B(_sd(_rN)));});},_sQ=function(_sR){var _sS=E(_sR);if(!_sS[0]){return [0];}else{var _sT=_sS[2],_sU=new T(function(){return B(_sQ(_sT));}),_sV=function(_sW){var _sX=E(_sW);if(!_sX[0]){return E(_sU);}else{var _sY=_sX[1],_sZ=_sX[2],_t0=new T(function(){return B(_sV(_sZ));}),_t1=new T(function(){return B(_rC(_sY));});return [1,_t1,_t0];}};return new F(function(){return _sV(B(_ez(2,B(_rL(_rH,_sS[1])))));});}},_t2=function(_t3,_t4){var _t5=E(_t4);if(!_t5[0]){return [0];}else{var _t6=_t5[1],_t7=_t5[2],_t8=new T(function(){var _t9=new T(function(){return B(A(_t3,[_t6]));}),_ta=B(_r6(_t9,_t7));return [0,_ta[1],_ta[2]];}),_tb=new T(function(){return B(_t2(_t3,E(_t8)[2]));}),_tc=new T(function(){return E(E(_t8)[1]);});return [1,[1,_t6,_tc],_tb];}},_td=function(_te,_tf){return E(E(_te)[1])==E(E(_tf)[1]);},_tg=function(_th,_ti){return new F(function(){return _3W(E(E(_th)[1]),E(E(_ti)[1]));});},_tj=42,_tk=function(_tl,_tm){return E(E(_tl)[2])==E(E(_tm)[2]);},_tn=function(_to,_tp,_tq,_tr){var _ts=E(_tr);if(!_ts[0]){var _tt=_ts[3],_tu=_ts[4],_tv=_ts[5],_tw=E(_ts[2]),_tx=E(_tw[1]);if(_to>=_tx){if(_to!=_tx){return new F(function(){return _9k(_tw,_tt,_tu,B(_tn(_to,_tp,_tq,_tv)));});}else{var _ty=E(_tw[2]);if(_tp>=_ty){if(_tp!=_ty){return new F(function(){return _9k(_tw,_tt,_tu,B(_tn(_to,_tp,_tq,_tv)));});}else{return [0,_ts[1],[0,_to,_tp],_tq,E(_tu),E(_tv)];}}else{return new F(function(){return _8B(_tw,_tt,B(_tn(_to,_tp,_tq,_tu)),_tv);});}}}else{return new F(function(){return _8B(_tw,_tt,B(_tn(_to,_tp,_tq,_tu)),_tv);});}}else{return [0,1,[0,_to,_tp],_tq,E(_8w),E(_8w)];}},_tz=function(_tA,_tB,_tC,_tD){var _tE=E(_tD);if(!_tE[0]){var _tF=_tE[3],_tG=_tE[4],_tH=_tE[5],_tI=E(_tE[2]),_tJ=E(_tI[1]);if(_tA>=_tJ){if(_tA!=_tJ){return new F(function(){return _9k(_tI,_tF,_tG,B(_tz(_tA,_tB,_tC,_tH)));});}else{var _tK=E(_tB),_tL=E(_tI[2]);if(_tK>=_tL){if(_tK!=_tL){return new F(function(){return _9k(_tI,_tF,_tG,B(_tn(_tA,_tK,_tC,_tH)));});}else{return [0,_tE[1],[0,_tA,_tK],_tC,E(_tG),E(_tH)];}}else{return new F(function(){return _8B(_tI,_tF,B(_tn(_tA,_tK,_tC,_tG)),_tH);});}}}else{return new F(function(){return _8B(_tI,_tF,B(_tz(_tA,_tB,_tC,_tG)),_tH);});}}else{return [0,1,[0,_tA,_tB],_tC,E(_8w),E(_8w)];}},_tM=function(_tN,_tO,_tP){var _tQ=new T(function(){return [1,_tN,_tQ];}),_tR=function(_tS){var _tT=E(_tS);if(!_tT[0]){return E(_tP);}else{var _tU=E(_tT[1]),_tV=E(_tU[1]),_tW=E(_tU[2]),_tX=E(_tV[1]),_tY=E(_tW[1]),_tZ=B(_tR(_tT[2]));if(_tX<=_tY){var _u0=B(_7H(E(_tV[2]),E(_tW[2]))),_u1=function(_u2,_u3){var _u4=new T(function(){return _u2==_tY;}),_u5=function(_u6,_u7){var _u8=E(_u6);if(!_u8[0]){if(!E(_u4)){return new F(function(){return _u1(_u2+1|0,_u7);});}else{return E(_tZ);}}else{var _u9=E(_u7);if(!_u9[0]){return E(_tZ);}else{return new F(function(){return _tz(_u2,_u8[1],_u9[1],B(_u5(_u8[2],_u9[2])));});}}};return new F(function(){return _u5(_u0,_u3);});};return new F(function(){return _u1(_tX,_tQ);});}else{return E(_tZ);}}};return new F(function(){return _tR(_tO);});},_ua=function(_ub){return E(E(_ub)[2]);},_uc=function(_){var _ud=B(_hL(0,_)),_ue=B(_hV(_ud,_)),_uf=_ue,_ug=B(_jA(_ud,_uf,_)),_uh=_ug,_ui=B(_kd(_ud,_uf,_)),_uj=_ui,_uk=B(_kQ(_ud,_uf,_)),_ul=_uk,_um=B(_lt(_ud,_uf,_)),_un=_um;return new T(function(){var _uo=new T(function(){var _up=new T(function(){var _uq=new T(function(){return B(_qr(_un));}),_ur=function(_us){var _ut=E(_us);if(!_ut[0]){return E(_uq);}else{var _uu=_ut[2],_uv=new T(function(){return B(_ur(_uu));},1);return new F(function(){return _1t(_ut[1],_uv);});}};return B(_ur(_ul));}),_uw=function(_ux){var _uy=E(_ux);if(!_uy[0]){return E(_up);}else{var _uz=_uy[2],_uA=new T(function(){return B(_uw(_uz));},1);return new F(function(){return _1t(_uy[1],_uA);});}};return B(_uw(_uj));}),_uB=function(_uC){var _uD=E(_uC);if(!_uD[0]){return E(_uo);}else{var _uE=_uD[2],_uF=new T(function(){return B(_uB(_uE));},1);return new F(function(){return _1t(_uD[1],_uF);});}},_uG=B(_uB(_uh)),_uH=B(_81(_qp,_uG)),_uI=new T(function(){return B(_81(_ua,_uG));}),_uJ=new T(function(){var _uK=function(_uL){while(1){var _uM=(function(_uN){var _uO=E(_uN);if(!_uO[0]){return [0];}else{var _uP=_uO[2],_uQ=E(_uO[1]),_uR=E(_uQ[1]),_uS=E(_uQ[2]);if(E(_uR[2])!=E(_uS[2])){_uL=_uP;return null;}else{var _uT=new T(function(){return B(_uK(_uP));}),_uU=new T(function(){if(!B(_qk(_3V,_uR,_uI))){return E(_uS);}else{return E(_uR);}});return [1,_uU,_uT];}}})(_uL);if(_uM!=null){return _uM;}}};return B(_sQ(B(_t2(_td,B(_rL(_tg,B(_uK(_uH))))))));}),_uV=function(_uW){var _uX=E(_uW);if(!_uX[0]){return E(_uJ);}else{var _uY=_uX[2],_uZ=new T(function(){return B(_uV(_uY));}),_v0=function(_v1){var _v2=E(_v1);if(!_v2[0]){return E(_uZ);}else{var _v3=_v2[1],_v4=_v2[2],_v5=new T(function(){return B(_v0(_v4));}),_v6=new T(function(){return B(_rC(_v3));});return [1,_v6,_v5];}};return new F(function(){return _v0(B(_ez(2,B(_rL(_tg,_uX[1])))));});}},_v7=function(_v8){while(1){var _v9=(function(_va){var _vb=E(_va);if(!_vb[0]){return [0];}else{var _vc=_vb[2],_vd=E(_vb[1]),_ve=E(_vd[1]),_vf=E(_vd[2]);if(E(_ve[1])!=E(_vf[1])){_v8=_vc;return null;}else{var _vg=new T(function(){return B(_v7(_vc));}),_vh=new T(function(){if(!B(_qk(_3V,_ve,_uI))){return E(_vf);}else{return E(_ve);}});return [1,_vh,_vg];}}})(_v8);if(_v9!=null){return _v9;}}},_vi=B(_tM(_qh,_uf,B(_tM(_tj,_uH,B(_tM(_tj,B(_uV(B(_t2(_tk,B(_rL(_rH,B(_v7(_uH)))))))),_qg)))))),_vj=function(_vk){var _vl=E(_vk);if(!_vl[0]){return E(_vi);}else{var _vm=_vl[2],_vn=E(_vl[1]),_vo=E(_vn[1]),_vp=E(_vn[2]);if(!B(_qk(_3V,_vo,_uI))){return new F(function(){return _eI(_vo[1],_vo[2],_qh,B(_vj(_vm)));});}else{return new F(function(){return _eI(_vp[1],_vp[2],_qh,B(_vj(_vm)));});}}};return B(_vj(_uH));});},_vq=new T(function(){return B(unCStr("!!: negative index"));}),_vr=new T(function(){return B(unCStr("Prelude."));}),_vs=new T(function(){return B(_1t(_vr,_vq));}),_vt=new T(function(){return B(err(_vs));}),_vu=new T(function(){return B(unCStr("!!: index too large"));}),_vv=new T(function(){return B(_1t(_vr,_vu));}),_vw=new T(function(){return B(err(_vv));}),_vx=function(_vy,_vz){while(1){var _vA=E(_vy);if(!_vA[0]){return E(_vw);}else{var _vB=E(_vz);if(!_vB){return E(_vA[1]);}else{_vy=_vA[2];_vz=_vB-1|0;continue;}}}},_vC=function(_vD,_vE){if(_vE>=0){return new F(function(){return _vx(_vD,_vE);});}else{return E(_vt);}},_vF=function(_vG,_vH){return new F(function(){return _vC(_vG,E(_vH));});},_vI=function(_vJ,_vK){while(1){var _vL=E(_vJ);if(!_vL[0]){return E(_vK);}else{_vJ=_vL[2];var _vM=_vK+1|0;_vK=_vM;continue;}}},_vN=new T(function(){return B(unCStr("Map.!: given key is not an element in the map"));}),_vO=new T(function(){return B(err(_vN));}),_vP=function(_vQ,_vR,_vS){while(1){var _vT=E(_vS);if(!_vT[0]){var _vU=_vT[4],_vV=_vT[5],_vW=E(_vT[2]),_vX=E(_vW[1]);if(_vQ>=_vX){if(_vQ!=_vX){_vS=_vV;continue;}else{var _vY=E(_vW[2]);if(_vR>=_vY){if(_vR!=_vY){_vS=_vV;continue;}else{return E(_vT[3]);}}else{_vS=_vU;continue;}}}else{_vS=_vU;continue;}}else{return E(_vO);}}},_vZ=function(_w0,_w1,_w2){while(1){var _w3=E(_w2);if(!_w3[0]){var _w4=_w3[4],_w5=_w3[5],_w6=E(_w3[2]),_w7=E(_w6[1]);if(_w0>=_w7){if(_w0!=_w7){_w2=_w5;continue;}else{var _w8=E(_w1),_w9=E(_w6[2]);if(_w8>=_w9){if(_w8!=_w9){return new F(function(){return _vP(_w0,_w8,_w5);});}else{return E(_w3[3]);}}else{return new F(function(){return _vP(_w0,_w8,_w4);});}}}else{_w2=_w4;continue;}}else{return E(_vO);}}},_wa=new T(function(){return B(_7H(0,20));}),_wb=function(_wc,_){var _wd=E(_gb)(),_we=_wd;return new T(function(){var _wf=function(_wg){var _wh=E(_wg);if(!_wh[0]){return [0];}else{var _wi=_wh[2],_wj=new T(function(){return B(_wf(_wi));}),_wk=E(_wa);if(!_wk[0]){return E(_wj);}else{var _wl=_wk[1],_wm=_wk[2],_wn=E(_wh[1]),_wo=_wn;if(E(B(_vZ(_wo,_wl,_wc)))==35){var _wp=new T(function(){var _wq=function(_wr){while(1){var _ws=(function(_wt){var _wu=E(_wt);if(!_wu[0]){return E(_wj);}else{var _wv=_wu[1],_ww=_wu[2];if(E(B(_vZ(_wo,_wv,_wc)))==35){var _wx=new T(function(){return B(_wq(_ww));});return [1,[0,_wn,_wv],_wx];}else{_wr=_ww;return null;}}})(_wr);if(_ws!=null){return _ws;}}};return B(_wq(_wm));});return [1,[0,_wn,_wl],_wp];}else{var _wy=function(_wz){while(1){var _wA=(function(_wB){var _wC=E(_wB);if(!_wC[0]){return E(_wj);}else{var _wD=_wC[1],_wE=_wC[2];if(E(B(_vZ(_wo,_wD,_wc)))==35){var _wF=new T(function(){return B(_wy(_wE));});return [1,[0,_wn,_wD],_wF];}else{_wz=_wE;return null;}}})(_wz);if(_wA!=null){return _wA;}}};return new F(function(){return _wy(_wm);});}}}},_wG=B(_wf(_wa));return B(_vF(_wG,B(_fV(0,B(_vI(_wG,0))-1|0,_we))[1]));});},_wH=46,_wI=new T(function(){return [1,_wH,_wI];}),_wJ=new T(function(){return B(_q7(_q4,_wI));}),_wK=new T(function(){return B(_pD(_wJ));}),_wL=function(_wM){var _wN=new T(function(){var _wO=E(_wM);if(_wO==255){return [0];}else{var _wP=B(_wL(_wO+1|0));return [1,_wP[1],_wP[2]];}});return [0,[0,_wM,_e7],_wN];},_wQ=[2],_wR=function(_wS,_wT){while(1){var _wU=E(_wT);if(!_wU[0]){return E(_wS);}else{var _wV=E(_wU[1]),_wW=B(_dG(E(_wV[1]),_wV[2],_wS));_wT=_wU[2];_wS=_wW;continue;}}},_wX=new T(function(){var _wY=B(_wL(0));return B(_wR(_wQ,[1,_wY[1],_wY[2]]));}),_wZ=new T(function(){return document;}),_x0=(function(e){return e.parentNode;}),_x1=(function(e,c) {return e.classList.contains(c);}),_x2=new T(function(){return B(unCStr("active"));}),_x3=function(_x4){return E(E(_x4)[1]);},_x5=function(_x6){return E(E(_x6)[1]);},_x7=function(_x8){return E(E(_x8)[2]);},_x9=function(_xa){return E(E(_xa)[1]);},_xb=function(_){return new F(function(){return nMV(_31);});},_xc=new T(function(){return B(_fP(_xb));}),_xd=(function(e,name,f){e.addEventListener(name,f,false);return [f];}),_xe=function(_){return new F(function(){return __jsNull();});},_xf=new T(function(){return B(_fP(_xe));}),_xg=new T(function(){return E(_xf);}),_xh=function(_xi){return E(E(_xi)[2]);},_xj=function(_xk,_xl,_xm,_xn,_xo,_xp){var _xq=B(_x3(_xk)),_xr=B(_x5(_xq)),_xs=new T(function(){return B(_b4(_xq));}),_xt=new T(function(){return B(_6T(_xr));}),_xu=new T(function(){return B(A(_b2,[_xl,_xn]));}),_xv=new T(function(){return B(A(_x9,[_xm,_xo]));}),_xw=function(_xx){return new F(function(){return A(_xt,[[0,_xv,_xu,_xx]]);});},_xy=function(_xz){var _xA=new T(function(){var _xB=new T(function(){var _xC=E(_xu),_xD=E(_xv),_xE=E(_xz),_xF=function(_xG,_){var _xH=B(A(_xE,[_xG,_]));return _xg;},_xI=__createJSFunc(2,E(_xF)),_xJ=_xI,_xK=function(_){return new F(function(){return E(_xd)(_xC,_xD,_xJ);});};return E(_xK);});return B(A(_xs,[_xB]));});return new F(function(){return A(_6x,[_xr,_xA,_xw]);});},_xL=new T(function(){var _xM=new T(function(){return B(_b4(_xq));}),_xN=function(_xO){var _xP=new T(function(){var _xQ=function(_){var _=wMV(E(_xc),[1,_xO]);return new F(function(){return A(_x7,[_xm,_xo,_xO,_]);});};return B(A(_xM,[_xQ]));});return new F(function(){return A(_6x,[_xr,_xP,_xp]);});};return B(A(_xh,[_xk,_xN]));});return new F(function(){return A(_6x,[_xr,_xL,_xy]);});},_xR=function(_){var _xS=B(_uc(_)),_xT=B(_wb(_xS,_)),_xU=nMV([0,_wX,_xT,_xT,_xS,_wK]),_xV=_xU,_xW=rMV(_xV),_xX=function(_xY,_){var _xZ=rMV(_xV),_y0=_xZ,_y1=new T(function(){var _y2=E(_y0),_y3=_y2[1],_y4=new T(function(){return B(_dG(E(_xY)[1],_ea,_y3));});return [0,_y4,_y2[2],_y2[3],_y2[4],_y2[5]];}),_=wMV(_xV,_y1),_y5=E(_7u),_y6=jsFind(_y5);if(!_y6[0]){return new F(function(){return _bf(_y5);});}else{var _y7=E(_x0)(E(_y6[1])),_y8=E(_x1)(_y7,toJSStr(E(_x2)));if(!_y8){return _b1;}else{var _y9=rMV(_xV),_ya=E(_y9),_yb=_ya[2],_yc=B(_d8(_yb,_ya[1],_yb,_ya[4],_ya[5],_)),_=wMV(_xV,E(E(_yc)[2]));return _b1;}}},_yd=B(A(_xj,[_3b,_w,_r,_wZ,_e8,_xX,_])),_ye=function(_yf,_){var _yg=rMV(_xV),_yh=_yg,_yi=new T(function(){var _yj=E(_yh),_yk=_yj[1],_yl=new T(function(){return B(_dG(E(_yf)[1],_e7,_yk));});return [0,_yl,_yj[2],_yj[3],_yj[4],_yj[5]];}),_=wMV(_xV,_yi);return _b1;},_ym=B(A(_xj,[_3b,_w,_r,_wZ,_e9,_ye,_])),_yn=rMV(_xV),_yo=E(_yn),_yp=_yo[2],_yq=B(_d8(_yp,_yo[1],_yp,_yo[4],_yo[5],_)),_=wMV(_xV,E(E(_yq)[2]));return _b1;},_yr=function(_){return new F(function(){return _xR(_);});};
var hasteMain = function() {B(A(_yr, [0]));};window.onload = hasteMain;