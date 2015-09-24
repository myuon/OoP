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

var _0="metaKey",_1="shiftKey",_2="altKey",_3="ctrlKey",_4="keyCode",_5=function(_6,_){var _7=_6[E(_4)],_8=_7,_9=_6[E(_3)],_a=_9,_b=_6[E(_2)],_c=_b,_d=_6[E(_1)],_e=_d,_f=_6[E(_0)],_g=_f;return new T(function(){var _h=Number(_8),_i=jsTrunc(_h);return [0,_i,E(_a),E(_c),E(_e),E(_g)];});},_j=function(_k,_l,_){return new F(function(){return _5(E(_l),_);});},_m="keydown",_n="keyup",_o="keypress",_p=function(_q){switch(E(_q)){case 0:return E(_o);case 1:return E(_n);default:return E(_m);}},_r=[0,_p,_j],_s=function(_t,_){return [1,_t];},_u=function(_v){return E(_v);},_w=[0,_u,_s],_x=function(_y,_z,_){var _A=B(A(_y,[_])),_B=B(A(_z,[_]));return _A;},_C=function(_D,_E,_){var _F=B(A(_D,[_])),_G=_F,_H=B(A(_E,[_])),_I=_H;return new T(function(){return B(A(_G,[_I]));});},_J=function(_K,_L,_){var _M=B(A(_L,[_]));return _K;},_N=function(_O,_P,_){var _Q=B(A(_P,[_])),_R=_Q;return new T(function(){return B(A(_O,[_R]));});},_S=[0,_N,_J],_T=function(_U,_){return _U;},_V=function(_W,_X,_){var _Y=B(A(_W,[_]));return new F(function(){return A(_X,[_]);});},_Z=[0,_S,_T,_C,_V,_x],_10=function(_11,_12,_){var _13=B(A(_11,[_]));return new F(function(){return A(_12,[_13,_]);});},_14=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_15=new T(function(){return B(unCStr("base"));}),_16=new T(function(){return B(unCStr("IOException"));}),_17=[0],_18=new T(function(){var _19=hs_wordToWord64(4053623282),_1a=hs_wordToWord64(3693590983);return [0,_19,_1a,[0,_19,_1a,_15,_14,_16],_17,_17];}),_1b=function(_1c){return E(_18);},_1d=function(_1e){return E(E(_1e)[1]);},_1f=function(_1g,_1h,_1i){var _1j=B(A(_1g,[_])),_1k=B(A(_1h,[_])),_1l=hs_eqWord64(_1j[1],_1k[1]);if(!_1l){return [0];}else{var _1m=hs_eqWord64(_1j[2],_1k[2]);return (!_1m)?[0]:[1,_1i];}},_1n=function(_1o){var _1p=E(_1o);return new F(function(){return _1f(B(_1d(_1p[1])),_1b,_1p[2]);});},_1q=new T(function(){return B(unCStr(": "));}),_1r=new T(function(){return B(unCStr(")"));}),_1s=new T(function(){return B(unCStr(" ("));}),_1t=function(_1u,_1v){var _1w=E(_1u);if(!_1w[0]){return E(_1v);}else{var _1x=_1w[2],_1y=new T(function(){return B(_1t(_1x,_1v));});return [1,_1w[1],_1y];}},_1z=new T(function(){return B(unCStr("interrupted"));}),_1A=new T(function(){return B(unCStr("system error"));}),_1B=new T(function(){return B(unCStr("unsatisified constraints"));}),_1C=new T(function(){return B(unCStr("user error"));}),_1D=new T(function(){return B(unCStr("permission denied"));}),_1E=new T(function(){return B(unCStr("illegal operation"));}),_1F=new T(function(){return B(unCStr("end of file"));}),_1G=new T(function(){return B(unCStr("resource exhausted"));}),_1H=new T(function(){return B(unCStr("resource busy"));}),_1I=new T(function(){return B(unCStr("does not exist"));}),_1J=new T(function(){return B(unCStr("already exists"));}),_1K=new T(function(){return B(unCStr("resource vanished"));}),_1L=new T(function(){return B(unCStr("timeout"));}),_1M=new T(function(){return B(unCStr("unsupported operation"));}),_1N=new T(function(){return B(unCStr("hardware fault"));}),_1O=new T(function(){return B(unCStr("inappropriate type"));}),_1P=new T(function(){return B(unCStr("invalid argument"));}),_1Q=new T(function(){return B(unCStr("failed"));}),_1R=new T(function(){return B(unCStr("protocol error"));}),_1S=function(_1T,_1U){switch(E(_1T)){case 0:return new F(function(){return _1t(_1J,_1U);});break;case 1:return new F(function(){return _1t(_1I,_1U);});break;case 2:return new F(function(){return _1t(_1H,_1U);});break;case 3:return new F(function(){return _1t(_1G,_1U);});break;case 4:return new F(function(){return _1t(_1F,_1U);});break;case 5:return new F(function(){return _1t(_1E,_1U);});break;case 6:return new F(function(){return _1t(_1D,_1U);});break;case 7:return new F(function(){return _1t(_1C,_1U);});break;case 8:return new F(function(){return _1t(_1B,_1U);});break;case 9:return new F(function(){return _1t(_1A,_1U);});break;case 10:return new F(function(){return _1t(_1R,_1U);});break;case 11:return new F(function(){return _1t(_1Q,_1U);});break;case 12:return new F(function(){return _1t(_1P,_1U);});break;case 13:return new F(function(){return _1t(_1O,_1U);});break;case 14:return new F(function(){return _1t(_1N,_1U);});break;case 15:return new F(function(){return _1t(_1M,_1U);});break;case 16:return new F(function(){return _1t(_1L,_1U);});break;case 17:return new F(function(){return _1t(_1K,_1U);});break;default:return new F(function(){return _1t(_1z,_1U);});}},_1V=new T(function(){return B(unCStr("}"));}),_1W=new T(function(){return B(unCStr("{handle: "));}),_1X=function(_1Y,_1Z,_20,_21,_22,_23){var _24=new T(function(){var _25=new T(function(){var _26=new T(function(){var _27=E(_21);if(!_27[0]){return E(_23);}else{var _28=new T(function(){var _29=new T(function(){return B(_1t(_1r,_23));},1);return B(_1t(_27,_29));},1);return B(_1t(_1s,_28));}},1);return B(_1S(_1Z,_26));},1),_2a=E(_20);if(!_2a[0]){return E(_25);}else{var _2b=new T(function(){return B(_1t(_1q,_25));},1);return B(_1t(_2a,_2b));}},1),_2c=E(_22);if(!_2c[0]){var _2d=E(_1Y);if(!_2d[0]){return E(_24);}else{var _2e=E(_2d[1]);if(!_2e[0]){var _2f=_2e[1],_2g=new T(function(){var _2h=new T(function(){var _2i=new T(function(){return B(_1t(_1q,_24));},1);return B(_1t(_1V,_2i));},1);return B(_1t(_2f,_2h));},1);return new F(function(){return _1t(_1W,_2g);});}else{var _2j=_2e[1],_2k=new T(function(){var _2l=new T(function(){var _2m=new T(function(){return B(_1t(_1q,_24));},1);return B(_1t(_1V,_2m));},1);return B(_1t(_2j,_2l));},1);return new F(function(){return _1t(_1W,_2k);});}}}else{var _2n=new T(function(){return B(_1t(_1q,_24));},1);return new F(function(){return _1t(_2c[1],_2n);});}},_2o=function(_2p){var _2q=E(_2p);return new F(function(){return _1X(_2q[1],_2q[2],_2q[3],_2q[4],_2q[6],_17);});},_2r=function(_2s,_2t,_2u){var _2v=E(_2t);return new F(function(){return _1X(_2v[1],_2v[2],_2v[3],_2v[4],_2v[6],_2u);});},_2w=function(_2x,_2y){var _2z=E(_2x);return new F(function(){return _1X(_2z[1],_2z[2],_2z[3],_2z[4],_2z[6],_2y);});},_2A=44,_2B=93,_2C=91,_2D=function(_2E,_2F,_2G){var _2H=E(_2F);if(!_2H[0]){return new F(function(){return unAppCStr("[]",_2G);});}else{var _2I=_2H[1],_2J=_2H[2],_2K=new T(function(){var _2L=new T(function(){var _2M=[1,_2B,_2G],_2N=function(_2O){var _2P=E(_2O);if(!_2P[0]){return E(_2M);}else{var _2Q=_2P[1],_2R=_2P[2],_2S=new T(function(){var _2T=new T(function(){return B(_2N(_2R));});return B(A(_2E,[_2Q,_2T]));});return [1,_2A,_2S];}};return B(_2N(_2J));});return B(A(_2E,[_2I,_2L]));});return [1,_2C,_2K];}},_2U=function(_2V,_2W){return new F(function(){return _2D(_2w,_2V,_2W);});},_2X=[0,_2r,_2o,_2U],_2Y=new T(function(){return [0,_1b,_2X,_2Z,_1n,_2o];}),_2Z=function(_30){return [0,_2Y,_30];},_31=[0],_32=7,_33=function(_34){return [0,_31,_32,_17,_34,_31,_31];},_35=function(_36,_){var _37=new T(function(){var _38=new T(function(){return B(_33(_36));});return B(_2Z(_38));});return new F(function(){return die(_37);});},_39=[0,_Z,_10,_V,_T,_35],_3a=[0,_39,_u],_3b=[0,_3a,_T],_3c="deltaZ",_3d="deltaY",_3e="deltaX",_3f=function(_3g,_3h){var _3i=jsShowI(_3g);return new F(function(){return _1t(fromJSStr(_3i),_3h);});},_3j=41,_3k=40,_3l=function(_3m,_3n,_3o){if(_3n>=0){return new F(function(){return _3f(_3n,_3o);});}else{if(_3m<=6){return new F(function(){return _3f(_3n,_3o);});}else{var _3p=new T(function(){var _3q=jsShowI(_3n);return B(_1t(fromJSStr(_3q),[1,_3j,_3o]));});return [1,_3k,_3p];}}},_3r=new T(function(){return B(unCStr(")"));}),_3s=new T(function(){return B(_3l(0,2,_3r));}),_3t=new T(function(){return B(unAppCStr(") is outside of enumeration\'s range (0,",_3s));}),_3u=function(_3v){var _3w=new T(function(){return B(_3l(0,_3v,_3t));});return new F(function(){return err(B(unAppCStr("toEnum{MouseButton}: tag (",_3w)));});},_3x=function(_3y,_){return new T(function(){var _3z=Number(E(_3y)),_3A=jsTrunc(_3z);if(_3A<0){return B(_3u(_3A));}else{if(_3A>2){return B(_3u(_3A));}else{return _3A;}}});},_3B=0,_3C=[0,_3B,_3B,_3B],_3D="button",_3E=new T(function(){return jsGetMouseCoords;}),_3F=function(_3G,_){var _3H=E(_3G);if(!_3H[0]){return _17;}else{var _3I=_3H[1],_3J=B(_3F(_3H[2],_)),_3K=new T(function(){var _3L=Number(E(_3I));return jsTrunc(_3L);});return [1,_3K,_3J];}},_3M=function(_3N,_){var _3O=__arr2lst(0,_3N);return new F(function(){return _3F(_3O,_);});},_3P=function(_3Q,_){return new F(function(){return _3M(E(_3Q),_);});},_3R=function(_3S,_){return new T(function(){var _3T=Number(E(_3S));return jsTrunc(_3T);});},_3U=[0,_3R,_3P],_3V=function(_3W,_){var _3X=E(_3W);if(!_3X[0]){return _17;}else{var _3Y=B(_3V(_3X[2],_));return [1,_3X[1],_3Y];}},_3Z=new T(function(){return B(unCStr("Pattern match failure in do expression at src/Haste/Prim/Any.hs:272:5-9"));}),_40=[0,_31,_32,_17,_3Z,_31,_31],_41=new T(function(){return B(_2Z(_40));}),_42=function(_){return new F(function(){return die(_41);});},_43=function(_44){return E(E(_44)[1]);},_45=function(_46,_47,_48,_){var _49=__arr2lst(0,_48),_4a=B(_3V(_49,_)),_4b=E(_4a);if(!_4b[0]){return new F(function(){return _42(_);});}else{var _4c=E(_4b[2]);if(!_4c[0]){return new F(function(){return _42(_);});}else{if(!E(_4c[2])[0]){var _4d=B(A(_43,[_46,_4b[1],_])),_4e=B(A(_43,[_47,_4c[1],_]));return [0,_4d,_4e];}else{return new F(function(){return _42(_);});}}}},_4f=function(_){return new F(function(){return __jsNull();});},_4g=function(_4h){var _4i=B(A(_4h,[_]));return E(_4i);},_4j=new T(function(){return B(_4g(_4f));}),_4k=new T(function(){return E(_4j);}),_4l=function(_4m,_4n,_){if(E(_4m)==7){var _4o=E(_3E)(_4n),_4p=B(_45(_3U,_3U,_4o,_)),_4q=_4p,_4r=_4n[E(_3e)],_4s=_4r,_4t=_4n[E(_3d)],_4u=_4t,_4v=_4n[E(_3c)],_4w=_4v;return new T(function(){return [0,E(_4q),E(_31),[0,_4s,_4u,_4w]];});}else{var _4x=E(_3E)(_4n),_4y=B(_45(_3U,_3U,_4x,_)),_4z=_4y,_4A=_4n[E(_3D)],_4B=__eq(_4A,E(_4k));if(!E(_4B)){var _4C=B(_3x(_4A,_)),_4D=_4C;return new T(function(){return [0,E(_4z),[1,_4D],E(_3C)];});}else{return new T(function(){return [0,E(_4z),E(_31),E(_3C)];});}}},_4E=function(_4F,_4G,_){return new F(function(){return _4l(_4F,E(_4G),_);});},_4H="mouseout",_4I="mouseover",_4J="mousemove",_4K="mouseup",_4L="mousedown",_4M="dblclick",_4N="click",_4O="wheel",_4P=function(_4Q){switch(E(_4Q)){case 0:return E(_4N);case 1:return E(_4M);case 2:return E(_4L);case 3:return E(_4K);case 4:return E(_4J);case 5:return E(_4I);case 6:return E(_4H);default:return E(_4O);}},_4R=[0,_4P,_4E],_4S=new T(function(){return B(unCStr("}"));}),_4T=new T(function(){return B(unCStr(", "));}),_4U=new T(function(){return B(unCStr("Escape"));}),_4V=new T(function(){return B(unCStr("Defence"));}),_4W=new T(function(){return B(unCStr("Attack"));}),_4X=function(_4Y){switch(E(_4Y)){case 0:return E(_4W);case 1:return E(_4V);default:return E(_4U);}},_4Z=function(_50,_51){switch(E(_50)){case 0:return new F(function(){return _1t(_4W,_51);});break;case 1:return new F(function(){return _1t(_4V,_51);});break;default:return new F(function(){return _1t(_4U,_51);});}},_52=function(_53,_54){return new F(function(){return _2D(_4Z,_53,_54);});},_55=function(_56,_57,_58){return new F(function(){return _4Z(_57,_58);});},_59=[0,_55,_4X,_52],_5a=new T(function(){return B(unCStr("commandMap = "));}),_5b=new T(function(){return B(unCStr("listSize = "));}),_5c=new T(function(){return B(unCStr("index = "));}),_5d=new T(function(){return B(unCStr("CommandList {"));}),_5e=function(_5f,_5g,_5h){var _5i=new T(function(){return B(A(_5g,[_5h]));});return new F(function(){return A(_5f,[[1,_2A,_5i]]);});},_5j=new T(function(){return B(unCStr("fromList "));}),_5k=new T(function(){return B(unCStr(": empty list"));}),_5l=new T(function(){return B(unCStr("Prelude."));}),_5m=function(_5n){var _5o=new T(function(){return B(_1t(_5n,_5k));},1);return new F(function(){return err(B(_1t(_5l,_5o)));});},_5p=new T(function(){return B(unCStr("foldr1"));}),_5q=new T(function(){return B(_5m(_5p));}),_5r=function(_5s,_5t){var _5u=E(_5t);if(!_5u[0]){return E(_5q);}else{var _5v=_5u[1],_5w=E(_5u[2]);if(!_5w[0]){return E(_5v);}else{var _5x=new T(function(){return B(_5r(_5s,_5w));});return new F(function(){return A(_5s,[_5v,_5x]);});}}},_5y=0,_5z=function(_5A){return E(E(_5A)[1]);},_5B=function(_5C,_5D){while(1){var _5E=(function(_5F,_5G){var _5H=E(_5G);switch(_5H[0]){case 0:var _5I=_5H[4],_5J=new T(function(){return B(_5B(_5F,_5I));});_5C=_5J;_5D=_5H[3];return null;case 1:return [1,[0,_5H[1],_5H[2]],_5F];default:return E(_5F);}})(_5C,_5D);if(_5E!=null){return _5E;}}},_5K=function(_5L){var _5M=E(_5L);if(!_5M[0]){var _5N=_5M[3],_5O=_5M[4];if(_5M[2]>=0){var _5P=new T(function(){return B(_5B(_17,_5O));});return new F(function(){return _5B(_5P,_5N);});}else{var _5Q=new T(function(){return B(_5B(_17,_5N));});return new F(function(){return _5B(_5Q,_5O);});}}else{return new F(function(){return _5B(_17,_5M);});}},_5R=function(_5S,_5T,_5U){var _5V=new T(function(){return B(_5K(_5U));}),_5W=function(_5X,_5Y){var _5Z=E(_5X),_60=_5Z[1],_61=_5Z[2],_62=new T(function(){var _63=new T(function(){return B(A(_5z,[_5S,_5y,_61]));}),_64=function(_65){return new F(function(){return _3l(0,E(_60),_65);});};return B(A(_5r,[_5e,[1,_64,[1,_63,_17]],[1,_3j,_5Y]]));});return [1,_3k,_62];};if(_5T<=10){var _66=function(_67){var _68=new T(function(){return B(_2D(_5W,_5V,_67));},1);return new F(function(){return _1t(_5j,_68);});};return E(_66);}else{var _69=function(_6a){var _6b=new T(function(){var _6c=new T(function(){return B(_2D(_5W,_5V,[1,_3j,_6a]));},1);return B(_1t(_5j,_6c));});return [1,_3k,_6b];};return E(_69);}},_6d=function(_6e,_6f,_6g,_6h){var _6i=new T(function(){return B(_5R(_59,0,_6h));}),_6j=function(_6k){var _6l=new T(function(){var _6m=new T(function(){var _6n=new T(function(){var _6o=new T(function(){var _6p=new T(function(){var _6q=new T(function(){var _6r=new T(function(){var _6s=new T(function(){var _6t=new T(function(){return B(_1t(_4S,_6k));});return B(A(_6i,[_6t]));},1);return B(_1t(_5a,_6s));},1);return B(_1t(_4T,_6r));});return B(_3l(0,E(_6g),_6q));},1);return B(_1t(_5b,_6p));},1);return B(_1t(_4T,_6o));});return B(_3l(0,E(_6f),_6n));},1);return B(_1t(_5c,_6m));},1);return new F(function(){return _1t(_5d,_6l);});};if(_6e<11){return E(_6j);}else{var _6u=function(_6v){var _6w=new T(function(){return B(_6j([1,_3j,_6v]));});return [1,_3k,_6w];};return E(_6u);}},_6x=new T(function(){return B(unCStr("_commandList = "));}),_6y=new T(function(){return B(unCStr("_mp = "));}),_6z=new T(function(){return B(unCStr("_intelligence = "));}),_6A=new T(function(){return B(unCStr("_strength = "));}),_6B=new T(function(){return B(unCStr("_name = "));}),_6C=new T(function(){return B(unCStr("Character {"));}),_6D=new T(function(){return B(unCStr("_maxMP = "));}),_6E=new T(function(){return B(unCStr("_hp = "));}),_6F=new T(function(){return B(unCStr("_maxHP = "));}),_6G=new T(function(){return B(unCStr("_level = "));}),_6H=new T(function(){return B(unCStr("_luck = "));}),_6I=new T(function(){return B(unCStr("_agility = "));}),_6J=new T(function(){return B(unCStr("_vitality = "));}),_6K=new T(function(){return B(unCStr("_technique = "));}),_6L=new T(function(){return B(unCStr("!!: negative index"));}),_6M=new T(function(){return B(_1t(_5l,_6L));}),_6N=new T(function(){return B(err(_6M));}),_6O=new T(function(){return B(unCStr("!!: index too large"));}),_6P=new T(function(){return B(_1t(_5l,_6O));}),_6Q=new T(function(){return B(err(_6P));}),_6R=function(_6S,_6T){while(1){var _6U=E(_6S);if(!_6U[0]){return E(_6Q);}else{var _6V=E(_6T);if(!_6V){return E(_6U[1]);}else{_6S=_6U[2];_6T=_6V-1|0;continue;}}}},_6W=function(_6X,_6Y){if(_6Y>=0){return new F(function(){return _6R(_6X,_6Y);});}else{return E(_6N);}},_6Z=new T(function(){return B(unCStr("ACK"));}),_70=new T(function(){return B(unCStr("BEL"));}),_71=new T(function(){return B(unCStr("BS"));}),_72=new T(function(){return B(unCStr("SP"));}),_73=[1,_72,_17],_74=new T(function(){return B(unCStr("US"));}),_75=[1,_74,_73],_76=new T(function(){return B(unCStr("RS"));}),_77=[1,_76,_75],_78=new T(function(){return B(unCStr("GS"));}),_79=[1,_78,_77],_7a=new T(function(){return B(unCStr("FS"));}),_7b=[1,_7a,_79],_7c=new T(function(){return B(unCStr("ESC"));}),_7d=[1,_7c,_7b],_7e=new T(function(){return B(unCStr("SUB"));}),_7f=[1,_7e,_7d],_7g=new T(function(){return B(unCStr("EM"));}),_7h=[1,_7g,_7f],_7i=new T(function(){return B(unCStr("CAN"));}),_7j=[1,_7i,_7h],_7k=new T(function(){return B(unCStr("ETB"));}),_7l=[1,_7k,_7j],_7m=new T(function(){return B(unCStr("SYN"));}),_7n=[1,_7m,_7l],_7o=new T(function(){return B(unCStr("NAK"));}),_7p=[1,_7o,_7n],_7q=new T(function(){return B(unCStr("DC4"));}),_7r=[1,_7q,_7p],_7s=new T(function(){return B(unCStr("DC3"));}),_7t=[1,_7s,_7r],_7u=new T(function(){return B(unCStr("DC2"));}),_7v=[1,_7u,_7t],_7w=new T(function(){return B(unCStr("DC1"));}),_7x=[1,_7w,_7v],_7y=new T(function(){return B(unCStr("DLE"));}),_7z=[1,_7y,_7x],_7A=new T(function(){return B(unCStr("SI"));}),_7B=[1,_7A,_7z],_7C=new T(function(){return B(unCStr("SO"));}),_7D=[1,_7C,_7B],_7E=new T(function(){return B(unCStr("CR"));}),_7F=[1,_7E,_7D],_7G=new T(function(){return B(unCStr("FF"));}),_7H=[1,_7G,_7F],_7I=new T(function(){return B(unCStr("VT"));}),_7J=[1,_7I,_7H],_7K=new T(function(){return B(unCStr("LF"));}),_7L=[1,_7K,_7J],_7M=new T(function(){return B(unCStr("HT"));}),_7N=[1,_7M,_7L],_7O=[1,_71,_7N],_7P=[1,_70,_7O],_7Q=[1,_6Z,_7P],_7R=new T(function(){return B(unCStr("ENQ"));}),_7S=[1,_7R,_7Q],_7T=new T(function(){return B(unCStr("EOT"));}),_7U=[1,_7T,_7S],_7V=new T(function(){return B(unCStr("ETX"));}),_7W=[1,_7V,_7U],_7X=new T(function(){return B(unCStr("STX"));}),_7Y=[1,_7X,_7W],_7Z=new T(function(){return B(unCStr("SOH"));}),_80=[1,_7Z,_7Y],_81=new T(function(){return B(unCStr("NUL"));}),_82=[1,_81,_80],_83=92,_84=new T(function(){return B(unCStr("\\DEL"));}),_85=new T(function(){return B(unCStr("\\a"));}),_86=new T(function(){return B(unCStr("\\\\"));}),_87=new T(function(){return B(unCStr("\\SO"));}),_88=new T(function(){return B(unCStr("\\r"));}),_89=new T(function(){return B(unCStr("\\f"));}),_8a=new T(function(){return B(unCStr("\\v"));}),_8b=new T(function(){return B(unCStr("\\n"));}),_8c=new T(function(){return B(unCStr("\\t"));}),_8d=new T(function(){return B(unCStr("\\b"));}),_8e=function(_8f,_8g){if(_8f<=127){var _8h=E(_8f);switch(_8h){case 92:return new F(function(){return _1t(_86,_8g);});break;case 127:return new F(function(){return _1t(_84,_8g);});break;default:if(_8h<32){var _8i=E(_8h);switch(_8i){case 7:return new F(function(){return _1t(_85,_8g);});break;case 8:return new F(function(){return _1t(_8d,_8g);});break;case 9:return new F(function(){return _1t(_8c,_8g);});break;case 10:return new F(function(){return _1t(_8b,_8g);});break;case 11:return new F(function(){return _1t(_8a,_8g);});break;case 12:return new F(function(){return _1t(_89,_8g);});break;case 13:return new F(function(){return _1t(_88,_8g);});break;case 14:var _8j=new T(function(){var _8k=E(_8g);if(!_8k[0]){return [0];}else{if(E(_8k[1])==72){return B(unAppCStr("\\&",_8k));}else{return E(_8k);}}},1);return new F(function(){return _1t(_87,_8j);});break;default:var _8l=new T(function(){return B(_6W(_82,_8i));});return new F(function(){return _1t([1,_83,_8l],_8g);});}}else{return [1,_8h,_8g];}}}else{var _8m=new T(function(){var _8n=jsShowI(_8f),_8o=new T(function(){var _8p=E(_8g);if(!_8p[0]){return [0];}else{var _8q=E(_8p[1]);if(_8q<48){return E(_8p);}else{if(_8q>57){return E(_8p);}else{return B(unAppCStr("\\&",_8p));}}}},1);return B(_1t(fromJSStr(_8n),_8o));});return [1,_83,_8m];}},_8r=new T(function(){return B(unCStr("\\\""));}),_8s=function(_8t,_8u){var _8v=E(_8t);if(!_8v[0]){return E(_8u);}else{var _8w=_8v[2],_8x=E(_8v[1]);if(_8x==34){var _8y=new T(function(){return B(_8s(_8w,_8u));},1);return new F(function(){return _1t(_8r,_8y);});}else{var _8z=new T(function(){return B(_8s(_8w,_8u));});return new F(function(){return _8e(_8x,_8z);});}}},_8A=34,_8B=function(_8C,_8D,_8E,_8F,_8G,_8H,_8I,_8J,_8K,_8L,_8M,_8N,_8O,_8P){var _8Q=new T(function(){var _8R=E(_8P);return B(_6d(0,_8R[1],_8R[2],_8R[3]));}),_8S=function(_8T){var _8U=new T(function(){var _8V=new T(function(){var _8W=new T(function(){var _8X=new T(function(){var _8Y=new T(function(){var _8Z=new T(function(){var _90=new T(function(){var _91=new T(function(){var _92=new T(function(){var _93=new T(function(){var _94=new T(function(){var _95=new T(function(){var _96=new T(function(){var _97=new T(function(){var _98=new T(function(){var _99=new T(function(){var _9a=new T(function(){var _9b=new T(function(){var _9c=new T(function(){var _9d=new T(function(){var _9e=new T(function(){var _9f=new T(function(){var _9g=new T(function(){var _9h=new T(function(){var _9i=new T(function(){var _9j=new T(function(){var _9k=new T(function(){var _9l=new T(function(){var _9m=new T(function(){var _9n=new T(function(){var _9o=new T(function(){var _9p=new T(function(){var _9q=new T(function(){var _9r=new T(function(){var _9s=new T(function(){var _9t=new T(function(){var _9u=new T(function(){var _9v=new T(function(){var _9w=new T(function(){return B(_1t(_4S,_8T));});return B(A(_8Q,[_9w]));},1);return B(_1t(_6x,_9v));},1);return B(_1t(_4T,_9u));});return B(_3l(0,E(_8O),_9t));},1);return B(_1t(_6y,_9s));},1);return B(_1t(_4T,_9r));});return B(_3l(0,E(_8N),_9q));},1);return B(_1t(_6D,_9p));},1);return B(_1t(_4T,_9o));});return B(_3l(0,E(_8M),_9n));},1);return B(_1t(_6E,_9m));},1);return B(_1t(_4T,_9l));});return B(_3l(0,E(_8L),_9k));},1);return B(_1t(_6F,_9j));},1);return B(_1t(_4T,_9i));});return B(_3l(0,E(_8K),_9h));},1);return B(_1t(_6G,_9g));},1);return B(_1t(_4T,_9f));});return B(_3l(0,E(_8J),_9e));},1);return B(_1t(_6H,_9d));},1);return B(_1t(_4T,_9c));});return B(_3l(0,E(_8I),_9b));},1);return B(_1t(_6I,_9a));},1);return B(_1t(_4T,_99));});return B(_3l(0,E(_8H),_98));},1);return B(_1t(_6J,_97));},1);return B(_1t(_4T,_96));});return B(_3l(0,E(_8G),_95));},1);return B(_1t(_6K,_94));},1);return B(_1t(_4T,_93));});return B(_3l(0,E(_8F),_92));},1);return B(_1t(_6z,_91));},1);return B(_1t(_4T,_90));});return B(_3l(0,E(_8E),_8Z));},1);return B(_1t(_6A,_8Y));},1);return B(_1t(_4T,_8X));});return B(_8s(_8D,[1,_8A,_8W]));});return B(_1t(_6B,[1,_8A,_8V]));},1);return new F(function(){return _1t(_6C,_8U);});};if(_8C<11){return E(_8S);}else{var _9x=function(_9y){var _9z=new T(function(){return B(_8S([1,_3j,_9y]));});return [1,_3k,_9z];};return E(_9x);}},_9A=function(_9B){var _9C=E(_9B);return new F(function(){return _8B(0,_9C[1],_9C[2],_9C[3],_9C[4],_9C[5],_9C[6],_9C[7],_9C[8],_9C[9],_9C[10],_9C[11],_9C[12],_9C[13]);});},_9D=function(_9E){var _9F=E(_9E);if(!_9F[0]){return [0,_17,_17];}else{var _9G=_9F[2],_9H=E(_9F[1]),_9I=new T(function(){var _9J=B(_9D(_9G));return [0,_9J[1],_9J[2]];}),_9K=new T(function(){return E(E(_9I)[2]);}),_9L=new T(function(){return E(E(_9I)[1]);});return [0,[1,_9H[1],_9L],[1,_9H[2],_9K]];}},_9M=function(_9N){var _9O=E(_9N);if(!_9O[0]){return [0,_17,_17];}else{var _9P=_9O[2],_9Q=E(_9O[1]),_9R=new T(function(){var _9S=B(_9M(_9P));return [0,_9S[1],_9S[2]];}),_9T=new T(function(){return E(E(_9R)[2]);}),_9U=new T(function(){return E(E(_9R)[1]);});return [0,[1,_9Q[1],_9U],[1,_9Q[2],_9T]];}},_9V=new T(function(){return B(unCStr("\n"));}),_9W=0,_9X=function(_9Y,_9Z,_){var _a0=jsWriteHandle(E(_9Y),toJSStr(E(_9Z)));return _9W;},_a1=function(_a2,_a3,_){var _a4=E(_a2),_a5=jsWriteHandle(_a4,toJSStr(E(_a3)));return new F(function(){return _9X(_a4,_9V,_);});},_a6=function(_a7,_a8){return (_a7>=_a8)?(_a7!=_a8)?2:1:0;},_a9=function(_aa,_ab){return new F(function(){return _a6(E(E(E(_aa)[2])[6]),E(E(E(_ab)[2])[6]));});},_ac=1,_ad=[0,_ac],_ae=new T(function(){return B(unCStr(" is not an element of the map"));}),_af=function(_ag){var _ah=new T(function(){return B(_1t(B(_3l(0,_ag,_17)),_ae));});return new F(function(){return err(B(unAppCStr("IntMap.!: key ",_ah)));});},_ai=function(_aj,_ak){var _al=_aj;while(1){var _am=E(_al);switch(_am[0]){case 0:var _an=_am[2]>>>0;if(((_ak>>>0&((_an-1>>>0^4294967295)>>>0^_an)>>>0)>>>0&4294967295)==_am[1]){if(!((_ak>>>0&_an)>>>0)){_al=_am[3];continue;}else{_al=_am[4];continue;}}else{return new F(function(){return _af(_ak);});}break;case 1:if(_ak!=_am[1]){return new F(function(){return _af(_ak);});}else{return E(_am[2]);}break;default:return new F(function(){return _af(_ak);});}}},_ao=function(_ap,_aq){return new F(function(){return _ai(_ap,E(_aq));});},_ar=0,_as=function(_at,_){var _au=E(_at);if(!_au[0]){return _17;}else{var _av=_au[1],_aw=B(_as(_au[2],_)),_ax=new T(function(){return E(E(_av)[13]);}),_ay=new T(function(){var _az=E(_av),_aA=new T(function(){var _aB=E(_ax),_aC=_aB[1],_aD=_aB[2],_aE=new T(function(){var _aF=E(_aC);if(_aF!=(E(_aD)-1|0)){return _aF+1|0;}else{return E(_ar);}});return [0,_aE,_aD,_aB[3]];});return [0,_az[1],_az[2],_az[3],_az[4],_az[5],_az[6],_az[7],_az[8],_az[9],_az[10],_az[11],_az[12],_aA];}),_aG=new T(function(){var _aH=E(_ax);return B(_ao(_aH[3],_aH[1]));});return [1,[0,_aG,_ay],_aw];}},_aI=function(_aJ,_){var _aK=E(_aJ);if(!_aK[0]){return _17;}else{var _aL=_aK[1],_aM=B(_aI(_aK[2],_)),_aN=new T(function(){return E(E(_aL)[13]);}),_aO=new T(function(){var _aP=E(_aL),_aQ=new T(function(){var _aR=E(_aN),_aS=_aR[1],_aT=_aR[2],_aU=new T(function(){var _aV=E(_aS);if(_aV!=(E(_aT)-1|0)){return _aV+1|0;}else{return E(_ar);}});return [0,_aU,_aT,_aR[3]];});return [0,_aP[1],_aP[2],_aP[3],_aP[4],_aP[5],_aP[6],_aP[7],_aP[8],_aP[9],_aP[10],_aP[11],_aP[12],_aQ];}),_aW=new T(function(){var _aX=E(_aN);return B(_ao(_aX[3],_aX[1]));});return [1,[0,_aW,_aO],_aM];}},_aY=function(_aZ,_b0){return E(_b0);},_b1=function(_b2,_b3){return E(_b3);},_b4=[0,_b1,_aY],_b5=function(_b6,_b7){return E(_b6);},_b8=function(_b9){return E(_b9);},_ba=[0,_b8,_b5],_bb=function(_bc){return E(_bc);},_bd=function(_be,_bf){while(1){var _bg=E(_bf);if(!_bg[0]){return [0];}else{var _bh=_bg[2],_bi=E(_be);if(_bi==1){return E(_bh);}else{_be=_bi-1|0;_bf=_bh;continue;}}}},_bj=function(_bk){return E(E(_bk)[1]);},_bl=function(_bm,_bn,_bo,_bp){var _bq=new T(function(){return E(_bm)-1|0;}),_br=new T(function(){return 0<E(_bq);}),_bs=new T(function(){var _bt=E(_bm)+1|0;if(_bt>0){return B(_bd(_bt,_bp));}else{return E(_bp);}}),_bu=new T(function(){var _bv=new T(function(){return B(_6W(_bp,E(_bm)));});return B(A(_bo,[_bv]));}),_bw=function(_bx){var _by=[1,_bx,_bs];if(!E(_br)){return E(_by);}else{var _bz=function(_bA,_bB){var _bC=E(_bA);if(!_bC[0]){return E(_by);}else{var _bD=_bC[1],_bE=_bC[2],_bF=E(_bB);if(_bF==1){return [1,_bD,_by];}else{var _bG=new T(function(){return B(_bz(_bE,_bF-1|0));});return [1,_bD,_bG];}}};return new F(function(){return _bz(_bp,E(_bq));});}};return new F(function(){return A(_bj,[_bn,_bw,_bu]);});},_bH=function(_bI,_bJ,_bK,_bL,_){while(1){var _bM=(function(_bN,_bO,_bP,_bQ,_){var _bR=E(_bN);if(!_bR[0]){return [0,_9W,[0,_bO,_bP,_bQ]];}else{var _bS=_bR[2],_bT=E(_bR[1]),_bU=_bT[2],_bV=E(_bT[1]);if(!_bV[0]){if(!E(_bV[1])){var _bW=new T(function(){var _bX=function(_bY){var _bZ=E(_bY),_c0=_bZ[10],_c1=new T(function(){return E(_c0)-((imul(E(E(_bU)[2]),5)|0)-(imul(E(B(_bl(_ar,_b4,_bb,_bO))[5]),2)|0)|0)|0;});return [0,_bZ[1],_bZ[2],_bZ[3],_bZ[4],_bZ[5],_bZ[6],_bZ[7],_bZ[8],_bZ[9],_c1,_bZ[11],_bZ[12],_bZ[13]];};return B(_bl(_ar,_ba,_bX,_bO));});_bI=_bS;_bJ=_bW;var _c2=_bP,_c3=_bQ;_bK=_c2;_bL=_c3;return null;}else{var _c4=new T(function(){var _c5=function(_c6){var _c7=E(_c6),_c8=_c7[10],_c9=new T(function(){return E(_c8)-((imul(E(E(_bU)[2]),5)|0)-(imul(E(B(_bl(_ar,_b4,_bb,_bP))[5]),2)|0)|0)|0;});return [0,_c7[1],_c7[2],_c7[3],_c7[4],_c7[5],_c7[6],_c7[7],_c7[8],_c7[9],_c9,_c7[11],_c7[12],_c7[13]];};return B(_bl(_ar,_ba,_c5,_bP));});_bI=_bS;var _ca=_bO;_bK=_c4;var _c3=_bQ;_bJ=_ca;_bL=_c3;return null;}}else{_bI=_bS;var _ca=_bO,_c2=_bP,_c3=_bQ;_bJ=_ca;_bK=_c2;_bL=_c3;return null;}}})(_bI,_bJ,_bK,_bL,_);if(_bM!=null){return _bM;}}},_cb=0,_cc=[0,_cb],_cd=function(_ce,_cf){var _cg=E(_ce);if(!_cg[0]){return [0];}else{var _ch=_cg[1],_ci=_cg[2],_cj=E(_cf);if(!_cj[0]){return [0];}else{var _ck=_cj[2],_cl=new T(function(){return B(_cd(_ci,_ck));}),_cm=new T(function(){var _cn=E(_ch);if(!_cn){return E(_cc);}else{return [1,_cn];}});return [1,[0,_cm,_cj[1]],_cl];}}},_co=[1,_17,_17],_cp=function(_cq,_cr){var _cs=function(_ct,_cu){var _cv=E(_ct);if(!_cv[0]){return E(_cu);}else{var _cw=_cv[1],_cx=_cv[2],_cy=E(_cu);if(!_cy[0]){return E(_cv);}else{var _cz=_cy[1],_cA=_cy[2];if(B(A(_cq,[_cw,_cz]))==2){var _cB=new T(function(){return B(_cs(_cv,_cA));});return [1,_cz,_cB];}else{var _cC=new T(function(){return B(_cs(_cx,_cy));});return [1,_cw,_cC];}}}},_cD=function(_cE){var _cF=E(_cE);if(!_cF[0]){return [0];}else{var _cG=_cF[1],_cH=E(_cF[2]);if(!_cH[0]){return E(_cF);}else{var _cI=_cH[1],_cJ=_cH[2],_cK=new T(function(){return B(_cD(_cJ));}),_cL=new T(function(){return B(_cs(_cG,_cI));});return [1,_cL,_cK];}}},_cM=new T(function(){return B(_cN(B(_cD(_17))));}),_cN=function(_cO){while(1){var _cP=E(_cO);if(!_cP[0]){return E(_cM);}else{if(!E(_cP[2])[0]){return E(_cP[1]);}else{_cO=B(_cD(_cP));continue;}}}},_cQ=new T(function(){return B(_cR(_17));}),_cS=function(_cT,_cU,_cV){while(1){var _cW=(function(_cX,_cY,_cZ){var _d0=E(_cZ);if(!_d0[0]){return [1,[1,_cX,_cY],_cQ];}else{var _d1=_d0[1];if(B(A(_cq,[_cX,_d1]))==2){_cT=_d1;var _d2=[1,_cX,_cY];_cV=_d0[2];_cU=_d2;return null;}else{var _d3=new T(function(){return B(_cR(_d0));});return [1,[1,_cX,_cY],_d3];}}})(_cT,_cU,_cV);if(_cW!=null){return _cW;}}},_d4=function(_d5,_d6,_d7){while(1){var _d8=(function(_d9,_da,_db){var _dc=E(_db);if(!_dc[0]){var _dd=new T(function(){return B(A(_da,[[1,_d9,_17]]));});return [1,_dd,_cQ];}else{var _de=_dc[1],_df=_dc[2];switch(B(A(_cq,[_d9,_de]))){case 0:var _dg=function(_dh){return new F(function(){return A(_da,[[1,_d9,_dh]]);});};_d5=_de;_d6=_dg;_d7=_df;return null;case 1:var _di=function(_dj){return new F(function(){return A(_da,[[1,_d9,_dj]]);});};_d5=_de;_d6=_di;_d7=_df;return null;default:var _dk=new T(function(){return B(_cR(_dc));}),_dl=new T(function(){return B(A(_da,[[1,_d9,_17]]));});return [1,_dl,_dk];}}})(_d5,_d6,_d7);if(_d8!=null){return _d8;}}},_cR=function(_dm){var _dn=E(_dm);if(!_dn[0]){return E(_co);}else{var _do=_dn[1],_dp=E(_dn[2]);if(!_dp[0]){return [1,_dn,_17];}else{var _dq=_dp[1],_dr=_dp[2];if(B(A(_cq,[_do,_dq]))==2){return new F(function(){return _cS(_dq,[1,_do,_17],_dr);});}else{var _ds=function(_dt){return [1,_do,_dt];};return new F(function(){return _d4(_dq,_ds,_dr);});}}}};return new F(function(){return _cN(B(_cR(_cr)));});},_du=function(_){return new F(function(){return jsMkStdout();});},_dv=new T(function(){return B(_4g(_du));}),_dw=function(_dx,_dy,_dz,_){var _dA=B(_aI(_dx,_)),_dB=B(_9M(_dA)),_dC=_dB[1],_dD=_dB[2],_dE=B(_as(_dy,_)),_dF=B(_9D(_dE))[2],_dG=new T(function(){return B(_cd(_dC,_dF));}),_dH=function(_dI,_dJ){var _dK=E(_dI);if(!_dK[0]){return E(_dG);}else{var _dL=_dK[1],_dM=_dK[2],_dN=E(_dJ);if(!_dN[0]){return E(_dG);}else{var _dO=_dN[2],_dP=new T(function(){return B(_dH(_dM,_dO));}),_dQ=new T(function(){var _dR=E(_dL);if(!_dR){return E(_ad);}else{return [1,_dR];}});return [1,[0,_dQ,_dN[1]],_dP];}}},_dS=new T(function(){return E(_dz)+1|0;}),_dT=B(_bH(B(_cp(_a9,B(_dH(_dC,_dD)))),_dD,_dF,_dS,_)),_dU=E(E(_dT)[2]),_dV=B(_a1(_dv,B(_2D(_9A,_dU[1],_17)),_)),_dW=B(_a1(_dv,B(_2D(_9A,_dU[2],_17)),_));return [0,_dW,_dU];},_dX=function(_dY,_dZ){if(_dY<=0){if(_dY>=0){return new F(function(){return quot(_dY,_dZ);});}else{if(_dZ<=0){return new F(function(){return quot(_dY,_dZ);});}else{return quot(_dY+1|0,_dZ)-1|0;}}}else{if(_dZ>=0){if(_dY>=0){return new F(function(){return quot(_dY,_dZ);});}else{if(_dZ<=0){return new F(function(){return quot(_dY,_dZ);});}else{return quot(_dY+1|0,_dZ)-1|0;}}}else{return quot(_dY-1|0,_dZ)-1|0;}}},_e0=new T(function(){return B(unCStr("GHC.Exception"));}),_e1=new T(function(){return B(unCStr("base"));}),_e2=new T(function(){return B(unCStr("ArithException"));}),_e3=new T(function(){var _e4=hs_wordToWord64(4194982440),_e5=hs_wordToWord64(3110813675);return [0,_e4,_e5,[0,_e4,_e5,_e1,_e0,_e2],_17,_17];}),_e6=function(_e7){return E(_e3);},_e8=function(_e9){var _ea=E(_e9);return new F(function(){return _1f(B(_1d(_ea[1])),_e6,_ea[2]);});},_eb=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_ec=new T(function(){return B(unCStr("denormal"));}),_ed=new T(function(){return B(unCStr("divide by zero"));}),_ee=new T(function(){return B(unCStr("loss of precision"));}),_ef=new T(function(){return B(unCStr("arithmetic underflow"));}),_eg=new T(function(){return B(unCStr("arithmetic overflow"));}),_eh=function(_ei,_ej){switch(E(_ei)){case 0:return new F(function(){return _1t(_eg,_ej);});break;case 1:return new F(function(){return _1t(_ef,_ej);});break;case 2:return new F(function(){return _1t(_ee,_ej);});break;case 3:return new F(function(){return _1t(_ed,_ej);});break;case 4:return new F(function(){return _1t(_ec,_ej);});break;default:return new F(function(){return _1t(_eb,_ej);});}},_ek=function(_el){return new F(function(){return _eh(_el,_17);});},_em=function(_en,_eo,_ep){return new F(function(){return _eh(_eo,_ep);});},_eq=function(_er,_es){return new F(function(){return _2D(_eh,_er,_es);});},_et=[0,_em,_ek,_eq],_eu=new T(function(){return [0,_e6,_et,_ev,_e8,_ek];}),_ev=function(_ew){return [0,_eu,_ew];},_ex=3,_ey=new T(function(){return B(_ev(_ex));}),_ez=new T(function(){return die(_ey);}),_eA=0,_eB=new T(function(){return B(_ev(_eA));}),_eC=new T(function(){return die(_eB);}),_eD=function(_eE,_eF){var _eG=E(_eF);switch(_eG){case -1:var _eH=E(_eE);if(_eH==(-2147483648)){return E(_eC);}else{return new F(function(){return _dX(_eH,-1);});}break;case 0:return E(_ez);default:return new F(function(){return _dX(_eE,_eG);});}},_eI=new T(function(){return B(unCStr("%"));}),_eJ=new T(function(){return B(unCStr("width"));}),_eK=function(_eL){return E(E(_eL)[1]);},_eM=function(_eN){return E(E(_eN)[2]);},_eO=function(_eP,_eQ,_eR,_eS,_eT){var _eU=function(_){var _eV=jsSetStyle(B(A(_eK,[_eP,_eR])),toJSStr(E(_eS)),toJSStr(E(_eT)));return _9W;};return new F(function(){return A(_eM,[_eQ,_eU]);});},_eW=function(_eX,_eY,_){while(1){var _eZ=(function(_f0,_f1,_){var _f2=E(_f0);if(!_f2[0]){return _9W;}else{var _f3=E(_f1);if(!_f3[0]){return _9W;}else{var _f4=_f3[1],_f5=new T(function(){var _f6=E(_f4);return B(_1t(B(_3l(0,B(_eD(imul(E(_f6[10]),100)|0,E(_f6[9]))),_17)),_eI));}),_f7=B(A(_eO,[_w,_3a,_f2[1],_eJ,_f5,_]));_eX=_f2[2];_eY=_f3[2];return null;}}})(_eX,_eY,_);if(_eZ!=null){return _eZ;}}},_f8=function(_f9,_fa,_){while(1){var _fb=(function(_fc,_fd,_){var _fe=E(_fc);if(!_fe[0]){return _9W;}else{var _ff=_fe[2],_fg=E(_fd);if(!_fg[0]){return _9W;}else{var _fh=_fg[2],_fi=E(_fg[1]),_fj=_fi[12],_fk=E(_fi[11]);if(!_fk){_f9=_ff;_fa=_fh;return null;}else{var _fl=new T(function(){var _fm=E(_fj),_fn=E(_fk);if(_fn==(-1)){var _fo=imul(_fm,100)|0;if(_fo==(-2147483648)){return E(_eC);}else{return B(_1t(B(_3l(0,B(_dX(_fo,-1)),_17)),_eI));}}else{return B(_1t(B(_3l(0,B(_dX(imul(_fm,100)|0,_fn)),_17)),_eI));}}),_fp=B(A(_eO,[_w,_3a,_fe[1],_eJ,_fl,_]));_f9=_ff;_fa=_fh;return null;}}}})(_f9,_fa,_);if(_fb!=null){return _fb;}}},_fq=new T(function(){return B(unCStr("innerHTML"));}),_fr=function(_fs,_ft,_fu,_fv,_fw){var _fx=function(_){var _fy=jsSet(B(A(_eK,[_fs,_fu])),toJSStr(E(_fv)),toJSStr(E(_fw)));return _9W;};return new F(function(){return A(_eM,[_ft,_fx]);});},_fz=function(_fA,_fB,_){while(1){var _fC=(function(_fD,_fE,_){var _fF=E(_fD);if(!_fF[0]){return _9W;}else{var _fG=E(_fE);if(!_fG[0]){return _9W;}else{var _fH=_fG[1],_fI=new T(function(){return E(E(_fH)[1]);}),_fJ=B(A(_fr,[_w,_3a,_fF[1],_fq,_fI,_]));_fA=_fF[2];_fB=_fG[2];return null;}}})(_fA,_fB,_);if(_fC!=null){return _fC;}}},_fK=function(_fL,_fM,_){while(1){var _fN=(function(_fO,_fP,_){var _fQ=E(_fO);if(!_fQ[0]){return _9W;}else{var _fR=E(_fP);if(!_fR[0]){return _9W;}else{var _fS=_fR[1],_fT=new T(function(){var _fU=E(_fS);return B(_1t(B(_3l(0,B(_eD(imul(E(_fU[10]),100)|0,E(_fU[9]))),_17)),_eI));}),_fV=B(A(_eO,[_w,_3a,_fQ[1],_eJ,_fT,_]));_fL=_fQ[2];_fM=_fR[2];return null;}}})(_fL,_fM,_);if(_fN!=null){return _fN;}}},_fW=new T(function(){return B(unCStr("#enemy-display-name"));}),_fX=new T(function(){return B(unCStr("#player-chara"));}),_fY=new T(function(){return B(unCStr("#enemy-display-hpratio"));}),_fZ=new T(function(){return B(unCStr("#player-display-mpratio"));}),_g0=function(_g1){return new F(function(){return _3l(0,E(E(_g1)[11]),_17);});},_g2=new T(function(){return B(unCStr("#player-display-maxmp"));}),_g3=function(_g4){return new F(function(){return _3l(0,E(E(_g4)[12]),_17);});},_g5=new T(function(){return B(unCStr("#player-display-mp"));}),_g6=new T(function(){return B(unCStr("#player-display-hpratio"));}),_g7=function(_g8){return new F(function(){return _3l(0,E(E(_g8)[9]),_17);});},_g9=new T(function(){return B(unCStr("#player-display-maxhp"));}),_ga=function(_gb){return new F(function(){return _3l(0,E(E(_gb)[10]),_17);});},_gc=new T(function(){return B(unCStr("#player-display-hp"));}),_gd=function(_ge){return E(E(_ge)[1]);},_gf=new T(function(){return B(unCStr("#player-display-name"));}),_gg=new T(function(){return B(unCStr("#enemy-chara"));}),_gh=function(_gi,_gj,_){var _gk=jsQuerySelectorAll(_gi,toJSStr(E(_fX))),_gl=new T(function(){return E(E(_gj)[1]);}),_gm=function(_,_gn){var _go=jsQuerySelectorAll(_gi,toJSStr(E(_gg))),_gp=new T(function(){return E(E(_gj)[2]);});if(!_go[0]){return _9W;}else{var _gq=E(_go[1]),_gr=E(_fW),_gs=jsQuerySelectorAll(_gq,toJSStr(_gr)),_gt=B(_fz(_gs,_gp,_)),_gu=E(_fY),_gv=jsQuerySelectorAll(_gq,toJSStr(_gu)),_gw=B(_fK(_gv,_gp,_)),_gx=_go[2],_=_;while(1){var _gy=E(_gx);if(!_gy[0]){return _9W;}else{var _gz=E(_gy[1]),_gA=jsQuerySelectorAll(_gz,toJSStr(_gr)),_gB=B(_fz(_gA,_gp,_)),_gC=jsQuerySelectorAll(_gz,toJSStr(_gu)),_gD=B(_fK(_gC,_gp,_));_gx=_gy[2];continue;}}}};if(!_gk[0]){return new F(function(){return _gm(_,_9W);});}else{var _gE=_gk[1],_gF=function(_gG,_gH,_){var _gI=jsQuerySelectorAll(E(_gE),toJSStr(E(_gG))),_gJ=_gI,_gK=_gl,_=_;while(1){var _gL=(function(_gM,_gN,_){var _gO=E(_gM);if(!_gO[0]){return _9W;}else{var _gP=E(_gN);if(!_gP[0]){return _9W;}else{var _gQ=_gP[1],_gR=new T(function(){return B(A(_gH,[_gQ]));}),_gS=B(A(_fr,[_w,_3a,_gO[1],_fq,_gR,_]));_gJ=_gO[2];_gK=_gP[2];return null;}}})(_gJ,_gK,_);if(_gL!=null){return _gL;}}},_gT=B(_gF(_gf,_gd,_)),_gU=B(_gF(_gc,_ga,_)),_gV=B(_gF(_g9,_g7,_)),_gW=E(_gE),_gX=E(_g6),_gY=jsQuerySelectorAll(_gW,toJSStr(_gX)),_gZ=B(_eW(_gY,_gl,_)),_h0=B(_gF(_g5,_g3,_)),_h1=B(_gF(_g2,_g0,_)),_h2=E(_fZ),_h3=jsQuerySelectorAll(_gW,toJSStr(_h2)),_h4=B(_f8(_h3,_gl,_)),_h5=function(_h6,_){while(1){var _h7=(function(_h8,_){var _h9=E(_h8);if(!_h9[0]){return _9W;}else{var _ha=_h9[1],_hb=function(_hc,_hd,_){var _he=jsQuerySelectorAll(E(_ha),toJSStr(E(_hc))),_hf=_he,_hg=_gl,_=_;while(1){var _hh=(function(_hi,_hj,_){var _hk=E(_hi);if(!_hk[0]){return _9W;}else{var _hl=E(_hj);if(!_hl[0]){return _9W;}else{var _hm=_hl[1],_hn=new T(function(){return B(A(_hd,[_hm]));}),_ho=B(A(_fr,[_w,_3a,_hk[1],_fq,_hn,_]));_hf=_hk[2];_hg=_hl[2];return null;}}})(_hf,_hg,_);if(_hh!=null){return _hh;}}},_hp=B(_hb(_gf,_gd,_)),_hq=B(_hb(_gc,_ga,_)),_hr=B(_hb(_g9,_g7,_)),_hs=E(_ha),_ht=jsQuerySelectorAll(_hs,toJSStr(_gX)),_hu=B(_eW(_ht,_gl,_)),_hv=B(_hb(_g5,_g3,_)),_hw=B(_hb(_g2,_g0,_)),_hx=jsQuerySelectorAll(_hs,toJSStr(_h2)),_hy=B(_f8(_hx,_gl,_));_h6=_h9[2];return null;}})(_h6,_);if(_h7!=null){return _h7;}}},_hz=B(_h5(_gk[2],_));return new F(function(){return _gm(_,_hz);});}},_hA=0,_hB=function(_hC){return E(E(_hC)[1]);},_hD=function(_hE){return E(E(_hE)[2]);},_hF=function(_hG){return new F(function(){return fromJSStr(E(_hG));});},_hH=function(_hI,_hJ,_hK,_hL){var _hM=function(_){return new F(function(){return jsGet(B(A(_eK,[_hI,_hK])),E(_hL));});};return new F(function(){return A(_eM,[_hJ,_hM]);});},_hN=function(_hO){return E(E(_hO)[4]);},_hP=function(_hQ,_hR,_hS,_hT){var _hU=B(_hB(_hR)),_hV=new T(function(){return B(_hN(_hU));}),_hW=function(_hX){var _hY=new T(function(){return B(_hF(_hX));});return new F(function(){return A(_hV,[_hY]);});},_hZ=new T(function(){var _i0=new T(function(){return toJSStr(E(_hT));});return B(_hH(_hQ,_hR,_hS,_i0));});return new F(function(){return A(_hD,[_hU,_hZ,_hW]);});},_i1=function(_i2,_i3,_){var _i4=B(A(_hP,[_w,_3a,_i2,_fq,_])),_i5=_i4,_i6=new T(function(){return B(_1t(_i5,_i3));});return new F(function(){return A(_fr,[_w,_3a,_i2,_fq,_i6,_]);});},_i7=new T(function(){return B(unCStr("  <div class=\"enemy\">"));}),_i8=new T(function(){return B(unCStr("    <span id=\"enemy-display-name\"></span><br>"));}),_i9=new T(function(){return B(unCStr("    HP"));}),_ia=new T(function(){return B(unCStr("    <div class=\"progress\">"));}),_ib=new T(function(){return B(unCStr("      <div class=\"progress-bar\" role=\"progressbar\" id=\"enemy-display-hpratio\">"));}),_ic=new T(function(){return B(unCStr("      </div>"));}),_id=new T(function(){return B(unCStr("    </div>"));}),_ie=new T(function(){return B(unCStr("</div>"));}),_if=[1,_ie,_17],_ig=new T(function(){return B(unCStr("  </div>"));}),_ih=[1,_ig,_if],_ii=[1,_id,_ih],_ij=[1,_ic,_ii],_ik=[1,_ib,_ij],_il=[1,_ia,_ik],_im=[1,_i9,_il],_in=[1,_i8,_im],_io=[1,_i7,_in],_ip=new T(function(){return B(unCStr("<div class=\"col-md-4\">"));}),_iq=function(_ir){var _is=E(_ir);if(!_is[0]){return [0];}else{var _it=_is[2],_iu=new T(function(){return B(_iq(_it));},1);return new F(function(){return _1t(_is[1],_iu);});}},_iv=function(_iw,_ix){var _iy=new T(function(){return B(_iq(_ix));},1);return new F(function(){return _1t(_iw,_iy);});},_iz=new T(function(){return B(_iv(_ip,_io));}),_iA=new T(function(){return B(unCStr("  <div class=\"player\">"));}),_iB=new T(function(){return B(unCStr("    <span id=\"player-display-name\"></span><br>"));}),_iC=new T(function(){return B(unCStr("    HP <span id=\"player-display-hp\"></span> / <span id=\"player-display-maxhp\"></span>"));}),_iD=new T(function(){return B(unCStr("      <div class=\"progress-bar\" role=\"progressbar\" id=\"player-display-hpratio\">"));}),_iE=new T(function(){return B(unCStr("      <div class=\"progress-bar progress-bar-info\" role=\"progressbar\" id=\"player-display-mpratio\">"));}),_iF=[1,_iE,_ij],_iG=[1,_ia,_iF],_iH=new T(function(){return B(unCStr("    MP <span id=\"player-display-mp\"></span> / <span id=\"player-display-maxmp\"></span>"));}),_iI=[1,_iH,_iG],_iJ=[1,_id,_iI],_iK=[1,_ic,_iJ],_iL=[1,_iD,_iK],_iM=[1,_ia,_iL],_iN=[1,_iC,_iM],_iO=[1,_iB,_iN],_iP=[1,_iA,_iO],_iQ=function(_iR){var _iS=E(_iR);if(!_iS[0]){return [0];}else{var _iT=_iS[2],_iU=new T(function(){return B(_iQ(_iT));},1);return new F(function(){return _1t(_iS[1],_iU);});}},_iV=function(_iW,_iX){var _iY=new T(function(){return B(_iQ(_iX));},1);return new F(function(){return _1t(_iW,_iY);});},_iZ=new T(function(){return B(_iV(_ip,_iP));}),_j0=new T(function(){return B(unCStr("Control.Exception.Base"));}),_j1=new T(function(){return B(unCStr("base"));}),_j2=new T(function(){return B(unCStr("PatternMatchFail"));}),_j3=new T(function(){var _j4=hs_wordToWord64(18445595),_j5=hs_wordToWord64(52003073);return [0,_j4,_j5,[0,_j4,_j5,_j1,_j0,_j2],_17,_17];}),_j6=function(_j7){return E(_j3);},_j8=function(_j9){var _ja=E(_j9);return new F(function(){return _1f(B(_1d(_ja[1])),_j6,_ja[2]);});},_jb=function(_jc){return E(E(_jc)[1]);},_jd=function(_je){return [0,_jf,_je];},_jg=function(_jh,_ji){return new F(function(){return _1t(E(_jh)[1],_ji);});},_jj=function(_jk,_jl){return new F(function(){return _2D(_jg,_jk,_jl);});},_jm=function(_jn,_jo,_jp){return new F(function(){return _1t(E(_jo)[1],_jp);});},_jq=[0,_jm,_jb,_jj],_jf=new T(function(){return [0,_j6,_jq,_jd,_j8,_jb];}),_jr=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_js=function(_jt){return E(E(_jt)[3]);},_ju=function(_jv,_jw){var _jx=new T(function(){return B(A(_js,[_jw,_jv]));});return new F(function(){return die(_jx);});},_jy=function(_jz,_ew){return new F(function(){return _ju(_jz,_ew);});},_jA=function(_jB,_jC){var _jD=E(_jC);if(!_jD[0]){return [0,_17,_17];}else{var _jE=_jD[1],_jF=_jD[2];if(!B(A(_jB,[_jE]))){return [0,_17,_jD];}else{var _jG=new T(function(){var _jH=B(_jA(_jB,_jF));return [0,_jH[1],_jH[2]];}),_jI=new T(function(){return E(E(_jG)[2]);}),_jJ=new T(function(){return E(E(_jG)[1]);});return [0,[1,_jE,_jJ],_jI];}}},_jK=32,_jL=new T(function(){return B(unCStr("\n"));}),_jM=function(_jN){return (E(_jN)==124)?false:true;},_jO=function(_jP,_jQ){var _jR=B(_jA(_jM,B(unCStr(_jP)))),_jS=_jR[1],_jT=function(_jU,_jV){var _jW=new T(function(){var _jX=new T(function(){var _jY=new T(function(){return B(_1t(_jV,_jL));},1);return B(_1t(_jQ,_jY));});return B(unAppCStr(": ",_jX));},1);return new F(function(){return _1t(_jU,_jW);});},_jZ=E(_jR[2]);if(!_jZ[0]){return new F(function(){return _jT(_jS,_17);});}else{if(E(_jZ[1])==124){return new F(function(){return _jT(_jS,[1,_jK,_jZ[2]]);});}else{return new F(function(){return _jT(_jS,_17);});}}},_k0=function(_k1){var _k2=new T(function(){return B(_jO(_k1,_jr));});return new F(function(){return _jy([0,_k2],_jf);});},_k3=function(_k4){return new F(function(){return _k0("Main.hs:(161,35)-(166,30)|lambda");});},_k5=new T(function(){return B(_k3(_));}),_k6=function(_k7){return new F(function(){return _k0("Main.hs:(155,35)-(157,41)|lambda");});},_k8=new T(function(){return B(_k6(_));}),_k9=function(_ka){return new F(function(){return _k0("Main.hs:(151,36)-(153,42)|lambda");});},_kb=new T(function(){return B(_k9(_));}),_kc=function(_kd){var _ke=new T(function(){return B(unCStr(_kd));});return new F(function(){return err(B(unAppCStr("Oops!  Entered absent arg ",_ke)));});},_kf=new T(function(){return B(_kc("ww_sqjR Int"));}),_kg=new T(function(){return B(unCStr("#step-battle"));}),_kh=function(_ki){return E(E(_ki)[1]);},_kj=function(_kk){return E(E(_kk)[2]);},_kl=function(_km){return E(E(_km)[1]);},_kn=function(_){return new F(function(){return nMV(_31);});},_ko=new T(function(){return B(_4g(_kn));}),_kp=(function(e,name,f){e.addEventListener(name,f,false);return [f];}),_kq=function(_kr){return E(E(_kr)[2]);},_ks=function(_kt,_ku,_kv,_kw,_kx,_ky){var _kz=B(_kh(_kt)),_kA=B(_hB(_kz)),_kB=new T(function(){return B(_eM(_kz));}),_kC=new T(function(){return B(_hN(_kA));}),_kD=new T(function(){return B(A(_eK,[_ku,_kw]));}),_kE=new T(function(){return B(A(_kl,[_kv,_kx]));}),_kF=function(_kG){return new F(function(){return A(_kC,[[0,_kE,_kD,_kG]]);});},_kH=function(_kI){var _kJ=new T(function(){var _kK=new T(function(){var _kL=E(_kD),_kM=E(_kE),_kN=E(_kI),_kO=function(_kP,_){var _kQ=B(A(_kN,[_kP,_]));return _4k;},_kR=__createJSFunc(2,E(_kO)),_kS=_kR,_kT=function(_){return new F(function(){return E(_kp)(_kL,_kM,_kS);});};return E(_kT);});return B(A(_kB,[_kK]));});return new F(function(){return A(_hD,[_kA,_kJ,_kF]);});},_kU=new T(function(){var _kV=new T(function(){return B(_eM(_kz));}),_kW=function(_kX){var _kY=new T(function(){var _kZ=function(_){var _=wMV(E(_ko),[1,_kX]);return new F(function(){return A(_kj,[_kv,_kx,_kX,_]);});};return B(A(_kV,[_kZ]));});return new F(function(){return A(_hD,[_kA,_kY,_ky]);});};return B(A(_kq,[_kt,_kW]));});return new F(function(){return A(_hD,[_kA,_kU,_kH]);});},_l0=function(_l1,_l2,_){var _l3=rMV(_l2),_l4=E(_l1),_l5=jsQuerySelectorAll(_l4,toJSStr(E(_fX))),_l6=E(E(_l3)[8]),_l7=_l6[1],_l8=_l6[2];if(!_l5[0]){return E(_kb);}else{var _l9=_l5[1];if(!E(_l5[2])[0]){var _la=function(_lb,_){while(1){var _lc=E(_lb);if(!_lc[0]){return _9W;}else{var _ld=B(_i1(_l9,_iZ,_));_lb=_lc[2];continue;}}},_le=B(_la(_l7,_)),_lf=jsQuerySelectorAll(_l4,toJSStr(E(_gg)));if(!_lf[0]){return E(_k8);}else{var _lg=_lf[1];if(!E(_lf[2])[0]){var _lh=function(_li,_){while(1){var _lj=E(_li);if(!_lj[0]){return _9W;}else{var _lk=B(_i1(_lg,_iz,_));_li=_lj[2];continue;}}},_ll=B(_lh(_l8,_)),_lm=B(_gh(_l4,[0,_l7,_l8,_kf],_)),_ln=jsQuerySelectorAll(_l4,toJSStr(E(_kg)));if(!_ln[0]){return E(_k5);}else{if(!E(_ln[2])[0]){var _lo=function(_lp,_){var _lq=rMV(_l2),_lr=E(_lq),_ls=E(_lr[8]),_lt=B(_dw(_ls[1],_ls[2],_ls[3],_)),_=wMV(_l2,[0,_lr[1],_lr[2],_lr[3],_lr[4],_lr[5],_lr[6],_lr[7],E(_lt)[2]]),_lu=rMV(_l2),_lv=_lu,_lw=new T(function(){return E(E(_lv)[8]);});return new F(function(){return _gh(_l4,_lw,_);});},_lx=B(A(_ks,[_3b,_w,_4R,_ln[1],_hA,_lo,_]));return _9W;}else{return E(_k5);}}}else{return E(_k8);}}}else{return E(_kb);}}},_ly=function(_lz,_lA,_lB,_lC){return (_lz!=_lB)?true:(E(_lA)!=E(_lC))?true:false;},_lD=function(_lE,_lF){var _lG=E(_lE),_lH=E(_lF);return new F(function(){return _ly(E(_lG[1]),_lG[2],E(_lH[1]),_lH[2]);});},_lI=function(_lJ,_lK){return E(_lJ)==E(_lK);},_lL=function(_lM,_lN,_lO,_lP){if(_lM!=_lO){return false;}else{return new F(function(){return _lI(_lN,_lP);});}},_lQ=function(_lR,_lS){var _lT=E(_lR),_lU=E(_lS);return new F(function(){return _lL(E(_lT[1]),_lT[2],E(_lU[1]),_lU[2]);});},_lV=[0,_lQ,_lD],_lW=function(_lX,_lY){return new F(function(){return _a6(E(_lX),E(_lY));});},_lZ=function(_m0,_m1,_m2,_m3){if(_m0>=_m2){if(_m0!=_m2){return 2;}else{return new F(function(){return _lW(_m1,_m3);});}}else{return 0;}},_m4=function(_m5,_m6){var _m7=E(_m5),_m8=E(_m6);return new F(function(){return _lZ(E(_m7[1]),_m7[2],E(_m8[1]),_m8[2]);});},_m9=function(_ma,_mb){return E(_ma)<E(_mb);},_mc=function(_md,_me,_mf,_mg){if(_md>=_mf){if(_md!=_mf){return false;}else{return new F(function(){return _m9(_me,_mg);});}}else{return true;}},_mh=function(_mi,_mj){var _mk=E(_mi),_ml=E(_mj);return new F(function(){return _mc(E(_mk[1]),_mk[2],E(_ml[1]),_ml[2]);});},_mm=function(_mn,_mo){return E(_mn)<=E(_mo);},_mp=function(_mq,_mr,_ms,_mt){if(_mq>=_ms){if(_mq!=_ms){return false;}else{return new F(function(){return _mm(_mr,_mt);});}}else{return true;}},_mu=function(_mv,_mw){var _mx=E(_mv),_my=E(_mw);return new F(function(){return _mp(E(_mx[1]),_mx[2],E(_my[1]),_my[2]);});},_mz=function(_mA,_mB){return E(_mA)>E(_mB);},_mC=function(_mD,_mE,_mF,_mG){if(_mD>=_mF){if(_mD!=_mF){return true;}else{return new F(function(){return _mz(_mE,_mG);});}}else{return false;}},_mH=function(_mI,_mJ){var _mK=E(_mI),_mL=E(_mJ);return new F(function(){return _mC(E(_mK[1]),_mK[2],E(_mL[1]),_mL[2]);});},_mM=function(_mN,_mO){return E(_mN)>=E(_mO);},_mP=function(_mQ,_mR,_mS,_mT){if(_mQ>=_mS){if(_mQ!=_mS){return true;}else{return new F(function(){return _mM(_mR,_mT);});}}else{return false;}},_mU=function(_mV,_mW){var _mX=E(_mV),_mY=E(_mW);return new F(function(){return _mP(E(_mX[1]),_mX[2],E(_mY[1]),_mY[2]);});},_mZ=function(_n0,_n1){var _n2=E(_n0),_n3=E(_n2[1]),_n4=E(_n1),_n5=E(_n4[1]);return (_n3>=_n5)?(_n3!=_n5)?E(_n2):(E(_n2[2])>E(_n4[2]))?E(_n2):E(_n4):E(_n4);},_n6=function(_n7,_n8){var _n9=E(_n7),_na=E(_n9[1]),_nb=E(_n8),_nc=E(_nb[1]);return (_na>=_nc)?(_na!=_nc)?E(_nb):(E(_n9[2])>E(_nb[2]))?E(_nb):E(_n9):E(_n9);},_nd=[0,_lV,_m4,_mh,_mu,_mH,_mU,_mZ,_n6],_ne=new T(function(){return B(unCStr("Map.!: given key is not an element in the map"));}),_nf=new T(function(){return B(err(_ne));}),_ng=function(_nh,_ni,_nj){while(1){var _nk=E(_nj);if(!_nk[0]){var _nl=_nk[4],_nm=_nk[5],_nn=E(_nk[2]),_no=E(_nn[1]);if(_nh>=_no){if(_nh!=_no){_nj=_nm;continue;}else{var _np=E(_nn[2]);if(_ni>=_np){if(_ni!=_np){_nj=_nm;continue;}else{return E(_nk[3]);}}else{_nj=_nl;continue;}}}else{_nj=_nl;continue;}}else{return E(_nf);}}},_nq=function(_nr,_ns,_nt,_){var _nu=B(A(_ns,[_nt,_])),_nv=_nu,_nw=new T(function(){return E(E(_nv)[2]);});return [0,_nr,_nw];},_nx=function(_ny,_nz,_nA,_){var _nB=B(A(_nz,[_nA,_])),_nC=_nB,_nD=new T(function(){return E(E(_nC)[2]);}),_nE=new T(function(){var _nF=new T(function(){return E(E(_nC)[1]);});return B(A(_ny,[_nF]));});return [0,_nE,_nD];},_nG=[0,_nx,_nq],_nH=function(_nI,_nJ,_nK,_){var _nL=B(A(_nI,[_nK,_])),_nM=_nL,_nN=new T(function(){return E(E(_nM)[2]);}),_nO=B(A(_nJ,[_nN,_])),_nP=_nO,_nQ=new T(function(){return E(E(_nP)[2]);}),_nR=new T(function(){var _nS=new T(function(){return E(E(_nP)[1]);});return B(A(E(_nM)[1],[_nS]));});return [0,_nR,_nQ];},_nT=function(_nU,_nV,_nW,_){var _nX=B(A(_nU,[_nW,_])),_nY=_nX,_nZ=new T(function(){return E(E(_nY)[2]);}),_o0=B(A(_nV,[_nZ,_])),_o1=_o0,_o2=new T(function(){return E(E(_o1)[2]);}),_o3=new T(function(){return E(E(_o1)[1]);});return [0,_o3,_o2];},_o4=function(_o5,_o6,_o7,_){var _o8=B(A(_o5,[_o7,_])),_o9=_o8,_oa=new T(function(){return E(E(_o9)[2]);}),_ob=B(A(_o6,[_oa,_])),_oc=_ob,_od=new T(function(){return E(E(_oc)[2]);}),_oe=new T(function(){return E(E(_o9)[1]);});return [0,_oe,_od];},_of=function(_og,_oh,_){return [0,_og,_oh];},_oi=[0,_nG,_of,_nH,_nT,_o4],_oj=function(_ok,_ol,_){return new F(function(){return _35(_ok,_);});},_om=function(_on,_oo,_op,_){var _oq=B(A(_on,[_op,_])),_or=_oq,_os=new T(function(){return E(E(_or)[2]);}),_ot=new T(function(){return E(E(_or)[1]);});return new F(function(){return A(_oo,[_ot,_os,_]);});},_ou=function(_ov,_ow,_ox,_oy,_oz){var _oA=function(_oB){var _oC=new T(function(){return E(E(_oB)[2]);}),_oD=new T(function(){return E(E(_oB)[1]);});return new F(function(){return A(_oy,[_oD,_oC]);});},_oE=new T(function(){return B(A(_ox,[_oz]));});return new F(function(){return A(_hD,[_ow,_oE,_oA]);});},_oF=function(_oG){return E(E(_oG)[5]);},_oH=function(_oI,_oJ,_oK){var _oL=new T(function(){return B(A(_oF,[_oJ,_oK]));}),_oM=function(_oN){return E(_oL);};return E(_oM);},_oO=function(_oP,_oQ){var _oR=function(_oS){return new F(function(){return _oH(_oP,_oQ,_oS);});},_oT=function(_oU,_oV){return new F(function(){return A(_hN,[_oQ,[0,_oU,_oV]]);});},_oW=function(_oX,_oS){return new F(function(){return _oY(_oP,_oQ,_oX,_oS);});},_oZ=function(_p0,_oX,_oS){return new F(function(){return _ou(_oP,_oQ,_p0,_oX,_oS);});};return [0,_oP,_oZ,_oW,_oT,_oR];},_oY=function(_p1,_p2,_p3,_p4){var _p5=function(_p6){return E(_p4);};return new F(function(){return A(_hD,[B(_oO(_p1,_p2)),_p3,_p5]);});},_p7=function(_p8,_p9){return new F(function(){return _oY(_oi,_39,_p8,_p9);});},_pa=[0,_oi,_om,_p7,_of,_oj],_pb=function(_pc,_pd,_){var _pe=B(A(_pc,[_]));return [0,_pe,_pd];},_pf=[0,_pa,_pb],_pg=function(_ph,_pi,_pj,_){while(1){var _pk=(function(_pl,_pm,_pn,_){var _po=E(_pl);if(!_po[0]){return [0,_9W,_pn];}else{var _pp=E(_pm);if(!_pp[0]){return [0,_9W,_pn];}else{var _pq=_pp[1],_pr=new T(function(){var _ps=E(_pq);return B(_1t(B(_3l(0,B(_eD(imul(E(_ps[10]),100)|0,E(_ps[9]))),_17)),_eI));}),_pt=B(A(_eO,[_w,_pf,_po[1],_eJ,_pr,_pn,_])),_pu=_pt,_pv=new T(function(){return E(E(_pu)[2]);});_ph=_po[2];_pi=_pp[2];_pj=_pv;return null;}}})(_ph,_pi,_pj,_);if(_pk!=null){return _pk;}}},_pw=function(_px,_py,_pz,_){while(1){var _pA=(function(_pB,_pC,_pD,_){var _pE=E(_pB);if(!_pE[0]){return [0,_9W,_pD];}else{var _pF=_pE[2],_pG=E(_pC);if(!_pG[0]){return [0,_9W,_pD];}else{var _pH=_pG[2],_pI=E(_pG[1]),_pJ=_pI[12],_pK=E(_pI[11]);if(!_pK){_px=_pF;_py=_pH;var _pL=_pD;_pz=_pL;return null;}else{var _pM=new T(function(){var _pN=E(_pJ),_pO=E(_pK);if(_pO==(-1)){var _pP=imul(_pN,100)|0;if(_pP==(-2147483648)){return E(_eC);}else{return B(_1t(B(_3l(0,B(_dX(_pP,-1)),_17)),_eI));}}else{return B(_1t(B(_3l(0,B(_dX(imul(_pN,100)|0,_pO)),_17)),_eI));}}),_pQ=B(A(_eO,[_w,_pf,_pE[1],_eJ,_pM,_pD,_])),_pR=_pQ,_pS=new T(function(){return E(E(_pR)[2]);});_px=_pF;_py=_pH;_pz=_pS;return null;}}}})(_px,_py,_pz,_);if(_pA!=null){return _pA;}}},_pT=function(_pU,_pV,_pW,_){while(1){var _pX=(function(_pY,_pZ,_q0,_){var _q1=E(_pY);if(!_q1[0]){return [0,_9W,_q0];}else{var _q2=E(_pZ);if(!_q2[0]){return [0,_9W,_q0];}else{var _q3=_q2[1],_q4=new T(function(){return E(E(_q3)[1]);}),_q5=B(A(_fr,[_w,_pf,_q1[1],_fq,_q4,_q0,_])),_q6=_q5,_q7=new T(function(){return E(E(_q6)[2]);});_pU=_q1[2];_pV=_q2[2];_pW=_q7;return null;}}})(_pU,_pV,_pW,_);if(_pX!=null){return _pX;}}},_q8=function(_q9,_qa,_qb,_){while(1){var _qc=(function(_qd,_qe,_qf,_){var _qg=E(_qd);if(!_qg[0]){return [0,_9W,_qf];}else{var _qh=E(_qe);if(!_qh[0]){return [0,_9W,_qf];}else{var _qi=_qh[1],_qj=new T(function(){var _qk=E(_qi);return B(_1t(B(_3l(0,B(_eD(imul(E(_qk[10]),100)|0,E(_qk[9]))),_17)),_eI));}),_ql=B(A(_eO,[_w,_pf,_qg[1],_eJ,_qj,_qf,_])),_qm=_ql,_qn=new T(function(){return E(E(_qm)[2]);});_q9=_qg[2];_qa=_qh[2];_qb=_qn;return null;}}})(_q9,_qa,_qb,_);if(_qc!=null){return _qc;}}},_qo=function(_qp,_qq,_qr,_){var _qs=jsQuerySelectorAll(_qp,toJSStr(E(_fX))),_qt=new T(function(){return E(E(_qq)[1]);});if(!_qs[0]){var _qu=jsQuerySelectorAll(_qp,toJSStr(E(_gg))),_qv=new T(function(){return E(E(_qq)[2]);});if(!_qu[0]){return [0,_9W,_qr];}else{var _qw=E(_qu[1]),_qx=E(_fW),_qy=jsQuerySelectorAll(_qw,toJSStr(_qx)),_qz=B(_pT(_qy,_qv,_qr,_)),_qA=_qz,_qB=E(_fY),_qC=jsQuerySelectorAll(_qw,toJSStr(_qB)),_qD=new T(function(){return E(E(_qA)[2]);}),_qE=B(_q8(_qC,_qv,_qD,_)),_qF=_qE,_qG=function(_qH,_qI,_){while(1){var _qJ=(function(_qK,_qL,_){var _qM=E(_qK);if(!_qM[0]){return [0,_9W,_qL];}else{var _qN=E(_qM[1]),_qO=jsQuerySelectorAll(_qN,toJSStr(_qx)),_qP=B(_pT(_qO,_qv,_qL,_)),_qQ=_qP,_qR=jsQuerySelectorAll(_qN,toJSStr(_qB)),_qS=new T(function(){return E(E(_qQ)[2]);}),_qT=B(_q8(_qR,_qv,_qS,_)),_qU=_qT,_qV=new T(function(){return E(E(_qU)[2]);});_qH=_qM[2];_qI=_qV;return null;}})(_qH,_qI,_);if(_qJ!=null){return _qJ;}}},_qW=new T(function(){return E(E(_qF)[2]);});return new F(function(){return _qG(_qu[2],_qW,_);});}}else{var _qX=_qs[1],_qY=function(_qZ,_r0,_r1,_){var _r2=jsQuerySelectorAll(E(_qX),toJSStr(E(_qZ))),_r3=_r2,_r4=_qt,_r5=_r1,_=_;while(1){var _r6=(function(_r7,_r8,_r9,_){var _ra=E(_r7);if(!_ra[0]){return [0,_9W,_r9];}else{var _rb=E(_r8);if(!_rb[0]){return [0,_9W,_r9];}else{var _rc=_rb[1],_rd=new T(function(){return B(A(_r0,[_rc]));}),_re=B(A(_fr,[_w,_pf,_ra[1],_fq,_rd,_r9,_])),_rf=_re,_rg=new T(function(){return E(E(_rf)[2]);});_r3=_ra[2];_r4=_rb[2];_r5=_rg;return null;}}})(_r3,_r4,_r5,_);if(_r6!=null){return _r6;}}},_rh=B(_qY(_gf,_gd,_qr,_)),_ri=_rh,_rj=new T(function(){return E(E(_ri)[2]);}),_rk=B(_qY(_gc,_ga,_rj,_)),_rl=_rk,_rm=new T(function(){return E(E(_rl)[2]);}),_rn=B(_qY(_g9,_g7,_rm,_)),_ro=_rn,_rp=E(_qX),_rq=E(_g6),_rr=jsQuerySelectorAll(_rp,toJSStr(_rq)),_rs=new T(function(){return E(E(_ro)[2]);}),_rt=B(_pg(_rr,_qt,_rs,_)),_ru=_rt,_rv=new T(function(){return E(E(_ru)[2]);}),_rw=B(_qY(_g5,_g3,_rv,_)),_rx=_rw,_ry=new T(function(){return E(E(_rx)[2]);}),_rz=B(_qY(_g2,_g0,_ry,_)),_rA=_rz,_rB=E(_fZ),_rC=jsQuerySelectorAll(_rp,toJSStr(_rB)),_rD=new T(function(){return E(E(_rA)[2]);}),_rE=B(_pw(_rC,_qt,_rD,_)),_rF=_rE,_rG=function(_rH,_rI,_){while(1){var _rJ=(function(_rK,_rL,_){var _rM=E(_rK);if(!_rM[0]){return [0,_9W,_rL];}else{var _rN=_rM[1],_rO=function(_rP,_rQ,_rR,_){var _rS=jsQuerySelectorAll(E(_rN),toJSStr(E(_rP))),_rT=_rS,_rU=_qt,_rV=_rR,_=_;while(1){var _rW=(function(_rX,_rY,_rZ,_){var _s0=E(_rX);if(!_s0[0]){return [0,_9W,_rZ];}else{var _s1=E(_rY);if(!_s1[0]){return [0,_9W,_rZ];}else{var _s2=_s1[1],_s3=new T(function(){return B(A(_rQ,[_s2]));}),_s4=B(A(_fr,[_w,_pf,_s0[1],_fq,_s3,_rZ,_])),_s5=_s4,_s6=new T(function(){return E(E(_s5)[2]);});_rT=_s0[2];_rU=_s1[2];_rV=_s6;return null;}}})(_rT,_rU,_rV,_);if(_rW!=null){return _rW;}}},_s7=B(_rO(_gf,_gd,_rL,_)),_s8=_s7,_s9=new T(function(){return E(E(_s8)[2]);}),_sa=B(_rO(_gc,_ga,_s9,_)),_sb=_sa,_sc=new T(function(){return E(E(_sb)[2]);}),_sd=B(_rO(_g9,_g7,_sc,_)),_se=_sd,_sf=E(_rN),_sg=jsQuerySelectorAll(_sf,toJSStr(_rq)),_sh=new T(function(){return E(E(_se)[2]);}),_si=B(_pg(_sg,_qt,_sh,_)),_sj=_si,_sk=new T(function(){return E(E(_sj)[2]);}),_sl=B(_rO(_g5,_g3,_sk,_)),_sm=_sl,_sn=new T(function(){return E(E(_sm)[2]);}),_so=B(_rO(_g2,_g0,_sn,_)),_sp=_so,_sq=jsQuerySelectorAll(_sf,toJSStr(_rB)),_sr=new T(function(){return E(E(_sp)[2]);}),_ss=B(_pw(_sq,_qt,_sr,_)),_st=_ss,_su=new T(function(){return E(E(_st)[2]);});_rH=_rM[2];_rI=_su;return null;}})(_rH,_rI,_);if(_rJ!=null){return _rJ;}}},_sv=new T(function(){return E(E(_rF)[2]);}),_sw=B(_rG(_qs[2],_sv,_)),_sx=_sw,_sy=jsQuerySelectorAll(_qp,toJSStr(E(_gg))),_sz=new T(function(){return E(E(_qq)[2]);});if(!_sy[0]){var _sA=new T(function(){return E(E(_sx)[2]);});return [0,_9W,_sA];}else{var _sB=E(_sy[1]),_sC=E(_fW),_sD=jsQuerySelectorAll(_sB,toJSStr(_sC)),_sE=new T(function(){return E(E(_sx)[2]);}),_sF=B(_pT(_sD,_sz,_sE,_)),_sG=_sF,_sH=E(_fY),_sI=jsQuerySelectorAll(_sB,toJSStr(_sH)),_sJ=new T(function(){return E(E(_sG)[2]);}),_sK=B(_q8(_sI,_sz,_sJ,_)),_sL=_sK,_sM=function(_sN,_sO,_){while(1){var _sP=(function(_sQ,_sR,_){var _sS=E(_sQ);if(!_sS[0]){return [0,_9W,_sR];}else{var _sT=E(_sS[1]),_sU=jsQuerySelectorAll(_sT,toJSStr(_sC)),_sV=B(_pT(_sU,_sz,_sR,_)),_sW=_sV,_sX=jsQuerySelectorAll(_sT,toJSStr(_sH)),_sY=new T(function(){return E(E(_sW)[2]);}),_sZ=B(_q8(_sX,_sz,_sY,_)),_t0=_sZ,_t1=new T(function(){return E(E(_t0)[2]);});_sN=_sS[2];_sO=_t1;return null;}})(_sN,_sO,_);if(_sP!=null){return _sP;}}},_t2=new T(function(){return E(E(_sL)[2]);});return new F(function(){return _sM(_sy[2],_t2,_);});}}},_t3=function(_t4,_t5,_t6,_){var _t7=B(A(_hP,[_w,_pf,_t4,_fq,_t6,_])),_t8=_t7,_t9=new T(function(){return E(E(_t8)[2]);}),_ta=new T(function(){return B(_1t(E(_t8)[1],_t5));});return new F(function(){return A(_fr,[_w,_pf,_t4,_fq,_ta,_t9,_]);});},_tb=function(_tc){return new F(function(){return _k0("Main.hs:(161,35)-(166,30)|lambda");});},_td=new T(function(){return B(_tb(_));}),_te=function(_tf){return new F(function(){return _k0("Main.hs:(155,35)-(157,41)|lambda");});},_tg=new T(function(){return B(_te(_));}),_th=function(_ti){return new F(function(){return _k0("Main.hs:(151,36)-(153,42)|lambda");});},_tj=new T(function(){return B(_th(_));}),_tk=new T(function(){return B(_kc("ww_sqmd Int"));}),_tl=function(_tm,_tn,_to,_){var _tp=rMV(_tn),_tq=E(_tm),_tr=jsQuerySelectorAll(_tq,toJSStr(E(_fX))),_ts=E(E(_tp)[8]),_tt=_ts[1],_tu=_ts[2];if(!_tr[0]){return E(_tj);}else{var _tv=_tr[1];if(!E(_tr[2])[0]){var _tw=function(_tx,_ty,_){while(1){var _tz=(function(_tA,_tB,_){var _tC=E(_tA);if(!_tC[0]){return [0,_9W,_tB];}else{var _tD=B(_t3(_tv,_iZ,_tB,_)),_tE=_tD,_tF=new T(function(){return E(E(_tE)[2]);});_tx=_tC[2];_ty=_tF;return null;}})(_tx,_ty,_);if(_tz!=null){return _tz;}}},_tG=B(_tw(_tt,_to,_)),_tH=_tG,_tI=jsQuerySelectorAll(_tq,toJSStr(E(_gg)));if(!_tI[0]){return E(_tg);}else{var _tJ=_tI[1];if(!E(_tI[2])[0]){var _tK=function(_tL,_tM,_){while(1){var _tN=(function(_tO,_tP,_){var _tQ=E(_tO);if(!_tQ[0]){return [0,_9W,_tP];}else{var _tR=B(_t3(_tJ,_iz,_tP,_)),_tS=_tR,_tT=new T(function(){return E(E(_tS)[2]);});_tL=_tQ[2];_tM=_tT;return null;}})(_tL,_tM,_);if(_tN!=null){return _tN;}}},_tU=new T(function(){return E(E(_tH)[2]);}),_tV=B(_tK(_tu,_tU,_)),_tW=_tV,_tX=new T(function(){return E(E(_tW)[2]);}),_tY=B(_qo(_tq,[0,_tt,_tu,_tk],_tX,_)),_tZ=_tY,_u0=jsQuerySelectorAll(_tq,toJSStr(E(_kg)));if(!_u0[0]){return E(_td);}else{if(!E(_u0[2])[0]){var _u1=function(_u2,_){var _u3=rMV(_tn),_u4=E(_u3),_u5=E(_u4[8]),_u6=B(_dw(_u5[1],_u5[2],_u5[3],_)),_=wMV(_tn,[0,_u4[1],_u4[2],_u4[3],_u4[4],_u4[5],_u4[6],_u4[7],E(_u6)[2]]),_u7=rMV(_tn),_u8=_u7,_u9=new T(function(){return E(E(_u8)[8]);});return new F(function(){return _gh(_tq,_u9,_);});},_ua=B(A(_ks,[_3b,_w,_4R,_u0[1],_hA,_u1,_])),_ub=new T(function(){return E(E(_tZ)[2]);});return [0,_9W,_ub];}else{return E(_td);}}}else{return E(_tg);}}}else{return E(_tj);}}},_uc=function(_ud,_ue,_uf){while(1){var _ug=E(_uf);if(!_ug[0]){var _uh=_ug[4],_ui=_ug[5],_uj=E(_ug[2]),_uk=E(_uj[1]);if(_ud>=_uk){if(_ud!=_uk){_uf=_ui;continue;}else{var _ul=E(_ue),_um=E(_uj[2]);if(_ul>=_um){if(_ul!=_um){_ue=_ul;_uf=_ui;continue;}else{return E(_ug[3]);}}else{_ue=_ul;_uf=_uh;continue;}}}else{_uf=_uh;continue;}}else{return E(_nf);}}},_un=new T(function(){return B(unCStr("&nbsp;"));}),_uo=new T(function(){return B(unCStr("@"));}),_up=new T(function(){return B(_1t(_un,_uo));}),_uq=function(_ur){var _us=E(_ur);if(_us==1){return E(_up);}else{var _ut=new T(function(){return B(_uq(_us-1|0));},1);return new F(function(){return _1t(_un,_ut);});}},_uu="dungeon-field",_uv="dungeon-battle",_uw=0,_ux=new T(function(){return document;}),_uy=function(){ $('#tabs a[href="#dungeon-battle"]').tab('show'); },_uz=(function(e){return e.parentNode;}),_uA=new T(function(){return B(unCStr("<br>"));}),_uB=function(_uC,_uD){if(_uC<=_uD){var _uE=function(_uF){var _uG=new T(function(){if(_uF!=_uD){return B(_uE(_uF+1|0));}else{return [0];}});return [1,_uF,_uG];};return new F(function(){return _uE(_uC);});}else{return [0];}},_uH=new T(function(){return B(_uB(0,34));}),_uI=new T(function(){return B(_uB(0,44));}),_uJ=function(_uK){var _uL=E(_uK);if(!_uL[0]){return [0];}else{var _uM=_uL[2],_uN=E(_uL[1]);if(E(_uN)==32){var _uO=new T(function(){return B(_uJ(_uM));},1);return new F(function(){return _1t(_un,_uO);});}else{var _uP=new T(function(){return B(_uJ(_uM));},1);return new F(function(){return _1t([1,_uN,_17],_uP);});}}},_uQ=function(_uR){var _uS=E(_uR);if(!_uS[0]){return [0];}else{var _uT=_uS[2],_uU=new T(function(){return B(_uQ(_uT));},1);return new F(function(){return _1t(_uS[1],_uU);});}},_uV=function(_uW,_uX){var _uY=E(_uX);if(!_uY[0]){return [0];}else{var _uZ=_uY[1],_v0=_uY[2],_v1=new T(function(){return B(_uV(_uW,_v0));}),_v2=new T(function(){return B(A(_uW,[_uZ]));});return [1,_v2,_v1];}},_v3=function(_v4,_v5){var _v6=E(_v5);if(!_v6[0]){return [0];}else{var _v7=_v6[2],_v8=new T(function(){return B(_v3(_v4,_v7));});return [1,_v4,[1,_v6[1],_v8]];}},_v9=function(_va){var _vb=function(_vc){var _vd=function(_ve,_vf){var _vg=E(_ve);if(!_vg[0]){return [0];}else{var _vh=_vg[1],_vi=_vg[2],_vj=E(_vf);if(_vj==1){var _vk=new T(function(){return B(_uc(E(_vh),_vc,_va));});return [1,_vk,_17];}else{var _vl=new T(function(){return B(_vd(_vi,_vj-1|0));}),_vm=new T(function(){return B(_uc(E(_vh),_vc,_va));});return [1,_vm,_vl];}}};return new F(function(){return _vd(_uI,45);});},_vn=B(_uV(_vb,_uH));if(!_vn[0]){return [0];}else{var _vo=_vn[2],_vp=new T(function(){return B(_v3(_uA,_vo));});return new F(function(){return _uJ(B(_uQ([1,_vn[1],_vp])));});}},_vq=[1],_vr=new T(function(){return B(unCStr("Failure in Data.Map.balanceL"));}),_vs=function(_vt){return new F(function(){return err(_vr);});},_vu=new T(function(){return B(_vs(_));}),_vv=function(_vw,_vx,_vy,_vz){var _vA=E(_vz);if(!_vA[0]){var _vB=_vA[1],_vC=E(_vy);if(!_vC[0]){var _vD=_vC[1],_vE=_vC[2],_vF=_vC[3];if(_vD<=(imul(3,_vB)|0)){return [0,(1+_vD|0)+_vB|0,E(_vw),_vx,E(_vC),E(_vA)];}else{var _vG=E(_vC[4]);if(!_vG[0]){var _vH=_vG[1],_vI=E(_vC[5]);if(!_vI[0]){var _vJ=_vI[1],_vK=_vI[2],_vL=_vI[3],_vM=_vI[4],_vN=_vI[5];if(_vJ>=(imul(2,_vH)|0)){var _vO=function(_vP){var _vQ=E(_vN);return (_vQ[0]==0)?[0,(1+_vD|0)+_vB|0,E(_vK),_vL,[0,(1+_vH|0)+_vP|0,E(_vE),_vF,E(_vG),E(_vM)],[0,(1+_vB|0)+_vQ[1]|0,E(_vw),_vx,E(_vQ),E(_vA)]]:[0,(1+_vD|0)+_vB|0,E(_vK),_vL,[0,(1+_vH|0)+_vP|0,E(_vE),_vF,E(_vG),E(_vM)],[0,1+_vB|0,E(_vw),_vx,E(_vq),E(_vA)]];},_vR=E(_vM);if(!_vR[0]){return new F(function(){return _vO(_vR[1]);});}else{return new F(function(){return _vO(0);});}}else{return [0,(1+_vD|0)+_vB|0,E(_vE),_vF,E(_vG),[0,(1+_vB|0)+_vJ|0,E(_vw),_vx,E(_vI),E(_vA)]];}}else{return E(_vu);}}else{return E(_vu);}}}else{return [0,1+_vB|0,E(_vw),_vx,E(_vq),E(_vA)];}}else{var _vS=E(_vy);if(!_vS[0]){var _vT=_vS[1],_vU=_vS[2],_vV=_vS[3],_vW=_vS[5],_vX=E(_vS[4]);if(!_vX[0]){var _vY=_vX[1],_vZ=E(_vW);if(!_vZ[0]){var _w0=_vZ[1],_w1=_vZ[2],_w2=_vZ[3],_w3=_vZ[4],_w4=_vZ[5];if(_w0>=(imul(2,_vY)|0)){var _w5=function(_w6){var _w7=E(_w4);return (_w7[0]==0)?[0,1+_vT|0,E(_w1),_w2,[0,(1+_vY|0)+_w6|0,E(_vU),_vV,E(_vX),E(_w3)],[0,1+_w7[1]|0,E(_vw),_vx,E(_w7),E(_vq)]]:[0,1+_vT|0,E(_w1),_w2,[0,(1+_vY|0)+_w6|0,E(_vU),_vV,E(_vX),E(_w3)],[0,1,E(_vw),_vx,E(_vq),E(_vq)]];},_w8=E(_w3);if(!_w8[0]){return new F(function(){return _w5(_w8[1]);});}else{return new F(function(){return _w5(0);});}}else{return [0,1+_vT|0,E(_vU),_vV,E(_vX),[0,1+_w0|0,E(_vw),_vx,E(_vZ),E(_vq)]];}}else{return [0,3,E(_vU),_vV,E(_vX),[0,1,E(_vw),_vx,E(_vq),E(_vq)]];}}else{var _w9=E(_vW);return (_w9[0]==0)?[0,3,E(_w9[2]),_w9[3],[0,1,E(_vU),_vV,E(_vq),E(_vq)],[0,1,E(_vw),_vx,E(_vq),E(_vq)]]:[0,2,E(_vw),_vx,E(_vS),E(_vq)];}}else{return [0,1,E(_vw),_vx,E(_vq),E(_vq)];}}},_wa=new T(function(){return B(unCStr("Failure in Data.Map.balanceR"));}),_wb=function(_wc){return new F(function(){return err(_wa);});},_wd=new T(function(){return B(_wb(_));}),_we=function(_wf,_wg,_wh,_wi){var _wj=E(_wh);if(!_wj[0]){var _wk=_wj[1],_wl=E(_wi);if(!_wl[0]){var _wm=_wl[1],_wn=_wl[2],_wo=_wl[3];if(_wm<=(imul(3,_wk)|0)){return [0,(1+_wk|0)+_wm|0,E(_wf),_wg,E(_wj),E(_wl)];}else{var _wp=E(_wl[4]);if(!_wp[0]){var _wq=_wp[1],_wr=_wp[2],_ws=_wp[3],_wt=_wp[4],_wu=_wp[5],_wv=E(_wl[5]);if(!_wv[0]){var _ww=_wv[1];if(_wq>=(imul(2,_ww)|0)){var _wx=function(_wy){var _wz=E(_wf),_wA=E(_wu);return (_wA[0]==0)?[0,(1+_wk|0)+_wm|0,E(_wr),_ws,[0,(1+_wk|0)+_wy|0,E(_wz),_wg,E(_wj),E(_wt)],[0,(1+_ww|0)+_wA[1]|0,E(_wn),_wo,E(_wA),E(_wv)]]:[0,(1+_wk|0)+_wm|0,E(_wr),_ws,[0,(1+_wk|0)+_wy|0,E(_wz),_wg,E(_wj),E(_wt)],[0,1+_ww|0,E(_wn),_wo,E(_vq),E(_wv)]];},_wB=E(_wt);if(!_wB[0]){return new F(function(){return _wx(_wB[1]);});}else{return new F(function(){return _wx(0);});}}else{return [0,(1+_wk|0)+_wm|0,E(_wn),_wo,[0,(1+_wk|0)+_wq|0,E(_wf),_wg,E(_wj),E(_wp)],E(_wv)];}}else{return E(_wd);}}else{return E(_wd);}}}else{return [0,1+_wk|0,E(_wf),_wg,E(_wj),E(_vq)];}}else{var _wC=E(_wi);if(!_wC[0]){var _wD=_wC[1],_wE=_wC[2],_wF=_wC[3],_wG=_wC[5],_wH=E(_wC[4]);if(!_wH[0]){var _wI=_wH[1],_wJ=_wH[2],_wK=_wH[3],_wL=_wH[4],_wM=_wH[5],_wN=E(_wG);if(!_wN[0]){var _wO=_wN[1];if(_wI>=(imul(2,_wO)|0)){var _wP=function(_wQ){var _wR=E(_wf),_wS=E(_wM);return (_wS[0]==0)?[0,1+_wD|0,E(_wJ),_wK,[0,1+_wQ|0,E(_wR),_wg,E(_vq),E(_wL)],[0,(1+_wO|0)+_wS[1]|0,E(_wE),_wF,E(_wS),E(_wN)]]:[0,1+_wD|0,E(_wJ),_wK,[0,1+_wQ|0,E(_wR),_wg,E(_vq),E(_wL)],[0,1+_wO|0,E(_wE),_wF,E(_vq),E(_wN)]];},_wT=E(_wL);if(!_wT[0]){return new F(function(){return _wP(_wT[1]);});}else{return new F(function(){return _wP(0);});}}else{return [0,1+_wD|0,E(_wE),_wF,[0,1+_wI|0,E(_wf),_wg,E(_vq),E(_wH)],E(_wN)];}}else{return [0,3,E(_wJ),_wK,[0,1,E(_wf),_wg,E(_vq),E(_vq)],[0,1,E(_wE),_wF,E(_vq),E(_vq)]];}}else{var _wU=E(_wG);return (_wU[0]==0)?[0,3,E(_wE),_wF,[0,1,E(_wf),_wg,E(_vq),E(_vq)],E(_wU)]:[0,2,E(_wf),_wg,E(_vq),E(_wC)];}}else{return [0,1,E(_wf),_wg,E(_vq),E(_vq)];}}},_wV=function(_wW){return E(E(_wW)[2]);},_wX=function(_wY,_wZ,_x0,_x1){var _x2=E(_wZ),_x3=E(_x1);if(!_x3[0]){var _x4=_x3[2],_x5=_x3[3],_x6=_x3[4],_x7=_x3[5];switch(B(A(_wV,[_wY,_x2,_x4]))){case 0:return new F(function(){return _vv(_x4,_x5,B(_wX(_wY,_x2,_x0,_x6)),_x7);});break;case 1:return [0,_x3[1],E(_x2),_x0,E(_x6),E(_x7)];default:return new F(function(){return _we(_x4,_x5,_x6,B(_wX(_wY,_x2,_x0,_x7)));});}}else{return [0,1,E(_x2),_x0,E(_vq),E(_vq)];}},_x8=function(_x9,_xa,_xb,_xc){return new F(function(){return _wX(_x9,_xa,_xb,_xc);});},_xd=function(_xe,_xf,_xg){var _xh=function(_xi){var _xj=E(_xi);if(!_xj[0]){return E(_xg);}else{var _xk=E(_xj[1]);return new F(function(){return _x8(_xe,_xk[1],_xk[2],B(_xh(_xj[2])));});}};return new F(function(){return _xh(_xf);});},_xl=new T(function(){return B(unCStr("block"));}),_xm=new T(function(){return B(unCStr("display"));}),_xn=function(_xo){return new F(function(){return _k0("Main.hs:(244,64)-(246,35)|lambda");});},_xp=new T(function(){return B(_xn(_));}),_xq=[1,_17,_17],_xr=function(_xs){var _xt=E(_xs);if(!_xt[0]){return E(_xq);}else{var _xu=_xt[2],_xv=new T(function(){return B(_xr(_xu));}),_xw=function(_xx){var _xy=E(_xx);if(!_xy[0]){return [0];}else{var _xz=_xy[1],_xA=_xy[2],_xB=new T(function(){return B(_xw(_xA));}),_xC=function(_xD){var _xE=E(_xD);if(!_xE[0]){return E(_xB);}else{var _xF=_xE[2],_xG=new T(function(){return B(_xC(_xF));});return [1,[1,_xz,_xE[1]],_xG];}};return new F(function(){return _xC(_xv);});}};return new F(function(){return _xw(_xt[1]);});}},_xH=function(_xI,_xJ){if(0>=_xI){return E(_xq);}else{var _xK=[1,_xJ,_17],_xL=function(_xM){var _xN=E(_xM);if(_xN==1){return E(_xK);}else{var _xO=new T(function(){return B(_xL(_xN-1|0));});return [1,_xJ,_xO];}};return new F(function(){return _xr(B(_xL(_xI)));});}},_xP=-2,_xQ=-1,_xR=1,_xS=2,_xT=[1,_xS,_17],_xU=[1,_xR,_xT],_xV=[1,_uw,_xU],_xW=[1,_xQ,_xV],_xX=[1,_xP,_xW],_xY=new T(function(){return B(_xH(2,_xX));}),_xZ=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:232:3-9"));}),_y0=[0,_31,_32,_17,_xZ,_31,_31],_y1=new T(function(){return B(_2Z(_y0));}),_y2=new T(function(){return B(unCStr("#tabs a[href=\"#dungeon-battle\"]"));}),_y3=new T(function(){return B(unCStr("player"));}),_y4=new T(function(){return B(unCStr(" found!"));}),_y5=function(_y6){var _y7=new T(function(){return B(_1t(fromJSStr(E(_y6)),_y4));});return new F(function(){return err(B(unAppCStr("No element with ID ",_y7)));});},_y8=function(_y9,_ya,_yb,_yc,_yd,_ye,_yf,_yg,_){var _yh=E(_yb),_yi=_yh[1],_yj=_yh[2],_yk=function(_,_yl,_ym,_yn,_yo,_yp,_yq,_yr,_ys,_yt){var _yu=function(_,_yv,_yw,_yx,_yy,_yz,_yA,_yB,_yC,_yD){var _yE=function(_,_yF,_yG,_yH,_yI,_yJ,_yK,_yL,_yM,_yN){var _yO=function(_,_yP,_yQ,_yR,_yS,_yT,_yU,_yV,_yW,_yX){var _yY=jsFind(toJSStr(E(_y3)));if(!_yY[0]){return new F(function(){return die(_y1);});}else{var _yZ=new T(function(){var _z0=function(_z1){while(1){var _z2=(function(_z3){var _z4=E(_z3);if(!_z4[0]){return [0];}else{var _z5=_z4[2],_z6=E(_z4[1]);if(!_z6[0]){_z1=_z5;return null;}else{var _z7=E(_z6[2]);if(!_z7[0]){_z1=_z5;return null;}else{if(!E(_z7[2])[0]){var _z8=E(_yQ),_z9=E(_z6[1]);if(0>(_z8+_z9|0)){var _za=function(_zb){while(1){var _zc=(function(_zd){var _ze=E(_zd);if(!_ze[0]){return [0];}else{var _zf=_ze[2],_zg=E(_ze[1]);if(!_zg[0]){_zb=_zf;return null;}else{var _zh=E(_zg[2]);if(!_zh[0]){_zb=_zf;return null;}else{if(!E(_zh[2])[0]){var _zi=E(_zg[1]);if(0>(_z8+_zi|0)){_zb=_zf;return null;}else{if((_z8+_zi|0)>44){_zb=_zf;return null;}else{var _zj=E(_yR),_zk=E(_zh[1]);if(0>(_zj+_zk|0)){_zb=_zf;return null;}else{if((_zj+_zk|0)>34){_zb=_zf;return null;}else{var _zl=new T(function(){return B(_za(_zf));}),_zm=_z8+_zi|0,_zn=_zj+_zk|0,_zo=new T(function(){return B(_ng(_zm,_zn,_yT));});return [1,[0,[0,_zm,_zn],_zo],_zl];}}}}}else{_zb=_zf;return null;}}}}})(_zb);if(_zc!=null){return _zc;}}};return new F(function(){return _za(_z5);});}else{if((_z8+_z9|0)>44){var _zp=function(_zq){while(1){var _zr=(function(_zs){var _zt=E(_zs);if(!_zt[0]){return [0];}else{var _zu=_zt[2],_zv=E(_zt[1]);if(!_zv[0]){_zq=_zu;return null;}else{var _zw=E(_zv[2]);if(!_zw[0]){_zq=_zu;return null;}else{if(!E(_zw[2])[0]){var _zx=E(_zv[1]);if(0>(_z8+_zx|0)){_zq=_zu;return null;}else{if((_z8+_zx|0)>44){_zq=_zu;return null;}else{var _zy=E(_yR),_zz=E(_zw[1]);if(0>(_zy+_zz|0)){_zq=_zu;return null;}else{if((_zy+_zz|0)>34){_zq=_zu;return null;}else{var _zA=new T(function(){return B(_zp(_zu));}),_zB=_z8+_zx|0,_zC=_zy+_zz|0,_zD=new T(function(){return B(_ng(_zB,_zC,_yT));});return [1,[0,[0,_zB,_zC],_zD],_zA];}}}}}else{_zq=_zu;return null;}}}}})(_zq);if(_zr!=null){return _zr;}}};return new F(function(){return _zp(_z5);});}else{var _zE=E(_yR),_zF=E(_z7[1]);if(0>(_zE+_zF|0)){var _zG=function(_zH){while(1){var _zI=(function(_zJ){var _zK=E(_zJ);if(!_zK[0]){return [0];}else{var _zL=_zK[2],_zM=E(_zK[1]);if(!_zM[0]){_zH=_zL;return null;}else{var _zN=E(_zM[2]);if(!_zN[0]){_zH=_zL;return null;}else{if(!E(_zN[2])[0]){var _zO=E(_zM[1]);if(0>(_z8+_zO|0)){_zH=_zL;return null;}else{if((_z8+_zO|0)>44){_zH=_zL;return null;}else{var _zP=E(_zN[1]);if(0>(_zE+_zP|0)){_zH=_zL;return null;}else{if((_zE+_zP|0)>34){_zH=_zL;return null;}else{var _zQ=new T(function(){return B(_zG(_zL));}),_zR=_z8+_zO|0,_zS=_zE+_zP|0,_zT=new T(function(){return B(_ng(_zR,_zS,_yT));});return [1,[0,[0,_zR,_zS],_zT],_zQ];}}}}}else{_zH=_zL;return null;}}}}})(_zH);if(_zI!=null){return _zI;}}};return new F(function(){return _zG(_z5);});}else{if((_zE+_zF|0)>34){var _zU=function(_zV){while(1){var _zW=(function(_zX){var _zY=E(_zX);if(!_zY[0]){return [0];}else{var _zZ=_zY[2],_A0=E(_zY[1]);if(!_A0[0]){_zV=_zZ;return null;}else{var _A1=E(_A0[2]);if(!_A1[0]){_zV=_zZ;return null;}else{if(!E(_A1[2])[0]){var _A2=E(_A0[1]);if(0>(_z8+_A2|0)){_zV=_zZ;return null;}else{if((_z8+_A2|0)>44){_zV=_zZ;return null;}else{var _A3=E(_A1[1]);if(0>(_zE+_A3|0)){_zV=_zZ;return null;}else{if((_zE+_A3|0)>34){_zV=_zZ;return null;}else{var _A4=new T(function(){return B(_zU(_zZ));}),_A5=_z8+_A2|0,_A6=_zE+_A3|0,_A7=new T(function(){return B(_ng(_A5,_A6,_yT));});return [1,[0,[0,_A5,_A6],_A7],_A4];}}}}}else{_zV=_zZ;return null;}}}}})(_zV);if(_zW!=null){return _zW;}}};return new F(function(){return _zU(_z5);});}else{var _A8=new T(function(){var _A9=function(_Aa){while(1){var _Ab=(function(_Ac){var _Ad=E(_Ac);if(!_Ad[0]){return [0];}else{var _Ae=_Ad[2],_Af=E(_Ad[1]);if(!_Af[0]){_Aa=_Ae;return null;}else{var _Ag=E(_Af[2]);if(!_Ag[0]){_Aa=_Ae;return null;}else{if(!E(_Ag[2])[0]){var _Ah=E(_Af[1]);if(0>(_z8+_Ah|0)){_Aa=_Ae;return null;}else{if((_z8+_Ah|0)>44){_Aa=_Ae;return null;}else{var _Ai=E(_Ag[1]);if(0>(_zE+_Ai|0)){_Aa=_Ae;return null;}else{if((_zE+_Ai|0)>34){_Aa=_Ae;return null;}else{var _Aj=new T(function(){return B(_A9(_Ae));}),_Ak=_z8+_Ah|0,_Al=_zE+_Ai|0,_Am=new T(function(){return B(_ng(_Ak,_Al,_yT));});return [1,[0,[0,_Ak,_Al],_Am],_Aj];}}}}}else{_Aa=_Ae;return null;}}}}})(_Aa);if(_Ab!=null){return _Ab;}}};return B(_A9(_z5));}),_An=_z8+_z9|0,_Ao=_zE+_zF|0,_Ap=new T(function(){return B(_ng(_An,_Ao,_yT));});return [1,[0,[0,_An,_Ao],_Ap],_A8];}}}}}else{_z1=_z5;return null;}}}}})(_z1);if(_z2!=null){return _z2;}}};return B(_xd(_nd,B(_z0(_xY)),_yU));}),_Aq=new T(function(){var _Ar=E(_yR);if(0>=_Ar){var _As=E(_yQ);if(0>=_As){return E(_uo);}else{return B(_uq(_As));}}else{var _At=new T(function(){var _Au=new T(function(){var _Av=E(_yQ);if(0>=_Av){return E(_uo);}else{return B(_uq(_Av));}},1);return B(_1t(_uA,_Au));}),_Aw=function(_Ax){var _Ay=E(_Ax);if(_Ay==1){return E(_At);}else{var _Az=new T(function(){return B(_Aw(_Ay-1|0));},1);return new F(function(){return _1t(_uA,_Az);});}};return B(_Aw(_Ar));}}),_AA=B(A(_fr,[_w,_pf,_yY[1],_fq,_Aq,[0,_yP,[0,_yQ,_yR],_yS,_yT,_yZ,_yV,_yW,_yX],_])),_AB=_AA,_AC=E(_uu),_AD=jsFind(_AC);if(!_AD[0]){return new F(function(){return _y5(_AC);});}else{var _AE=new T(function(){return E(E(_AB)[2]);}),_AF=new T(function(){var _AG=new T(function(){return E(E(_AE)[5]);});return B(_v9(_AG));}),_AH=B(A(_fr,[_w,_pf,_AD[1],_fq,_AF,_AE,_])),_AI=E(E(_AH)[2]);if(E(_AI[6])==5){var _AJ=E(_uy)(E(_4k)),_AK=jsQuerySelectorAll(E(_ux),toJSStr(E(_y2)));if(!_AK[0]){return E(_xp);}else{if(!E(_AK[2])[0]){var _AL=E(_uz)(E(_AK[1])),_AM=B(A(_eO,[_w,_pf,_AL,_xm,_xl,[0,_AI[1],_AI[2],_AI[3],_AI[4],_AI[5],_uw,_AI[7],_AI[8]],_])),_AN=_AM,_AO=E(_uv),_AP=jsFind(_AO);if(!_AP[0]){return new F(function(){return _y5(_AO);});}else{var _AQ=new T(function(){return E(E(_AN)[2]);});return new F(function(){return _tl(_AP[1],E(_y9),_AQ,_);});}}else{return E(_xp);}}}else{return [0,_9W,_AI];}}}};if(!B(_ai(_ya,39))){return new F(function(){return _yO(_,_yF,_yG,_yH,_yI,_yJ,_yK,_yL,_yM,_yN);});}else{var _AR=E(_yG),_AS=_AR+1|0;switch(E(B(_uc(_AS,_yH,_yJ)))){case 35:var _AT=new T(function(){return E(_yL)+1|0;});return new F(function(){return _yO(_,_yF,_AS,_yH,_yI,_yJ,_yK,_AT,_yM,_yN);});break;case 45:var _AU=new T(function(){return E(_yL)+1|0;});return new F(function(){return _yO(_,_yF,_AS,_yH,_yI,_yJ,_yK,_AU,_yM,_yN);});break;default:return new F(function(){return _yO(_,_yF,_AR,_yH,_yI,_yJ,_yK,_yL,_yM,_yN);});}}};if(!B(_ai(_ya,37))){return new F(function(){return _yE(_,_yv,_yw,_yx,_yy,_yz,_yA,_yB,_yC,_yD);});}else{var _AV=E(_yw),_AW=_AV+(-1)|0;switch(E(B(_uc(_AW,_yx,_yz)))){case 35:var _AX=new T(function(){return E(_yB)+1|0;});return new F(function(){return _yE(_,_yv,_AW,_yx,_yy,_yz,_yA,_AX,_yC,_yD);});break;case 45:var _AY=new T(function(){return E(_yB)+1|0;});return new F(function(){return _yE(_,_yv,_AW,_yx,_yy,_yz,_yA,_AY,_yC,_yD);});break;default:return new F(function(){return _yE(_,_yv,_AV,_yx,_yy,_yz,_yA,_yB,_yC,_yD);});}}};if(!B(_ai(_ya,40))){return new F(function(){return _yu(_,_yl,_ym,_yn,_yo,_yp,_yq,_yr,_ys,_yt);});}else{var _AZ=E(_ym),_B0=new T(function(){return E(_yn)+1|0;});switch(E(B(_uc(_AZ,_B0,_yp)))){case 35:var _B1=new T(function(){return E(_yr)+1|0;});return new F(function(){return _yu(_,_yl,_AZ,_B0,_yo,_yp,_yq,_B1,_ys,_yt);});break;case 45:var _B2=new T(function(){return E(_yr)+1|0;});return new F(function(){return _yu(_,_yl,_AZ,_B0,_yo,_yp,_yq,_B2,_ys,_yt);});break;default:return new F(function(){return _yu(_,_yl,_AZ,_yn,_yo,_yp,_yq,_yr,_ys,_yt);});}}};if(!B(_ai(_ya,38))){return new F(function(){return _yk(_,_ya,_yi,_yj,_yh,_yc,_yd,_ye,_yf,_yg);});}else{var _B3=E(_yi),_B4=new T(function(){return E(_yj)+(-1)|0;});switch(E(B(_uc(_B3,_B4,_yc)))){case 35:var _B5=new T(function(){return E(_ye)+1|0;});return new F(function(){return _yk(_,_ya,_B3,_B4,_yh,_yc,_yd,_B5,_yf,_yg);});break;case 45:var _B6=new T(function(){return E(_ye)+1|0;});return new F(function(){return _yk(_,_ya,_B3,_B4,_yh,_yc,_yd,_B6,_yf,_yg);});break;default:return new F(function(){return _yk(_,_ya,_B3,_yj,_yh,_yc,_yd,_ye,_yf,_yg);});}}},_B7=function(_B8,_B9,_Ba){var _Bb=E(_Ba);switch(_Bb[0]){case 0:var _Bc=_Bb[1],_Bd=_Bb[2],_Be=_Bb[3],_Bf=_Bb[4],_Bg=_Bd>>>0;if(((_B8>>>0&((_Bg-1>>>0^4294967295)>>>0^_Bg)>>>0)>>>0&4294967295)==_Bc){return ((_B8>>>0&_Bg)>>>0==0)?[0,_Bc,_Bd,E(B(_B7(_B8,_B9,_Be))),E(_Bf)]:[0,_Bc,_Bd,E(_Be),E(B(_B7(_B8,_B9,_Bf)))];}else{var _Bh=(_B8>>>0^_Bc>>>0)>>>0,_Bi=(_Bh|_Bh>>>1)>>>0,_Bj=(_Bi|_Bi>>>2)>>>0,_Bk=(_Bj|_Bj>>>4)>>>0,_Bl=(_Bk|_Bk>>>8)>>>0,_Bm=(_Bl|_Bl>>>16)>>>0,_Bn=(_Bm^_Bm>>>1)>>>0&4294967295,_Bo=_Bn>>>0;return ((_B8>>>0&_Bo)>>>0==0)?[0,(_B8>>>0&((_Bo-1>>>0^4294967295)>>>0^_Bo)>>>0)>>>0&4294967295,_Bn,[1,_B8,_B9],E(_Bb)]:[0,(_B8>>>0&((_Bo-1>>>0^4294967295)>>>0^_Bo)>>>0)>>>0&4294967295,_Bn,E(_Bb),[1,_B8,_B9]];}break;case 1:var _Bp=_Bb[1];if(_B8!=_Bp){var _Bq=(_B8>>>0^_Bp>>>0)>>>0,_Br=(_Bq|_Bq>>>1)>>>0,_Bs=(_Br|_Br>>>2)>>>0,_Bt=(_Bs|_Bs>>>4)>>>0,_Bu=(_Bt|_Bt>>>8)>>>0,_Bv=(_Bu|_Bu>>>16)>>>0,_Bw=(_Bv^_Bv>>>1)>>>0&4294967295,_Bx=_Bw>>>0;return ((_B8>>>0&_Bx)>>>0==0)?[0,(_B8>>>0&((_Bx-1>>>0^4294967295)>>>0^_Bx)>>>0)>>>0&4294967295,_Bw,[1,_B8,_B9],E(_Bb)]:[0,(_B8>>>0&((_Bx-1>>>0^4294967295)>>>0^_Bx)>>>0)>>>0&4294967295,_Bw,E(_Bb),[1,_B8,_B9]];}else{return [1,_B8,_B9];}break;default:return [1,_B8,_B9];}},_By=0,_Bz=false,_BA=0,_BB=1,_BC=true,_BD=function(_BE,_BF){while(1){var _BG=E(_BF);if(!_BG[0]){return [0];}else{var _BH=_BG[2],_BI=E(_BE);if(_BI==1){return E(_BH);}else{_BE=_BI-1|0;_BF=_BH;continue;}}}},_BJ=function(_BK,_BL,_BM){var _BN=E(_BK);if(_BN==1){return E(_BM);}else{return new F(function(){return _BD(_BN-1|0,_BM);});}},_BO=function(_BP,_BQ){var _BR=E(_BQ);if(!_BR[0]){return [0];}else{var _BS=_BR[1],_BT=_BR[2],_BU=E(_BP);if(_BU==1){return [1,_BS,_17];}else{var _BV=new T(function(){return B(_BO(_BU-1|0,_BT));});return [1,_BS,_BV];}}},_BW=function(_BX,_BY,_BZ){var _C0=new T(function(){if(_BX>0){return B(_C1(_BX,B(_BJ(_BX,_BY,_BZ))));}else{return B(_BW(_BX,_BY,_BZ));}}),_C2=new T(function(){if(0>=_BX){return [0];}else{return B(_BO(_BX,[1,_BY,_BZ]));}});return [1,_C2,_C0];},_C1=function(_C3,_C4){var _C5=E(_C4);if(!_C5[0]){return [0];}else{var _C6=_C5[1],_C7=_C5[2],_C8=new T(function(){if(_C3>0){return B(_C1(_C3,B(_BJ(_C3,_C6,_C7))));}else{return B(_BW(_C3,_C6,_C7));}}),_C9=new T(function(){if(0>=_C3){return [0];}else{return B(_BO(_C3,_C5));}});return [1,_C9,_C8];}},_Ca=function(_Cb,_Cc,_Cd,_Ce){var _Cf=E(_Ce);if(!_Cf[0]){var _Cg=_Cf[3],_Ch=_Cf[4],_Ci=_Cf[5],_Cj=E(_Cf[2]),_Ck=E(_Cb),_Cl=E(_Cj[1]);if(_Ck>=_Cl){if(_Ck!=_Cl){return new F(function(){return _we(_Cj,_Cg,_Ch,B(_Ca(_Ck,_Cc,_Cd,_Ci)));});}else{var _Cm=E(_Cc),_Cn=E(_Cj[2]);if(_Cm>=_Cn){if(_Cm!=_Cn){return new F(function(){return _we(_Cj,_Cg,_Ch,B(_Ca(_Ck,_Cm,_Cd,_Ci)));});}else{return [0,_Cf[1],[0,_Ck,_Cm],_Cd,E(_Ch),E(_Ci)];}}else{return new F(function(){return _vv(_Cj,_Cg,B(_Ca(_Ck,_Cm,_Cd,_Ch)),_Ci);});}}}else{return new F(function(){return _vv(_Cj,_Cg,B(_Ca(_Ck,_Cc,_Cd,_Ch)),_Ci);});}}else{return [0,1,[0,_Cb,_Cc],_Cd,E(_vq),E(_vq)];}},_Co=function(_Cp){var _Cq=E(_Cp);if(!_Cq[0]){return [0];}else{var _Cr=_Cq[2],_Cs=new T(function(){return B(_Co(_Cr));},1);return new F(function(){return _1t(_Cq[1],_Cs);});}},_Ct=function(_Cu){return new F(function(){return _Co(_Cu);});},_Cv=(function(s){return s[0];}),_Cw=function(_Cx,_Cy){var _Cz=_Cx%_Cy;if(_Cx<=0){if(_Cx>=0){return E(_Cz);}else{if(_Cy<=0){return E(_Cz);}else{var _CA=E(_Cz);return (_CA==0)?0:_CA+_Cy|0;}}}else{if(_Cy>=0){if(_Cx>=0){return E(_Cz);}else{if(_Cy<=0){return E(_Cz);}else{var _CB=E(_Cz);return (_CB==0)?0:_CB+_Cy|0;}}}else{var _CC=E(_Cz);return (_CC==0)?0:_CC+_Cy|0;}}},_CD=(function(s){var ba = window['newByteArr'](16);ba['v']['w32'][0] = s[0];ba['v']['w32'][1] = s[1];ba['v']['w32'][2] = s[2];ba['v']['w32'][3] = s[3];return window['md51'](ba,16);}),_CE=function(_CF){var _CG=function(_){return new F(function(){return E(_CD)(E(_CF));});};return new F(function(){return _4g(_CG);});},_CH=function(_CI,_CJ,_CK){while(1){var _CL=(function(_CM,_CN,_CO){if(_CM>_CN){var _CP=_CN,_CQ=_CM,_CR=_CO;_CI=_CP;_CJ=_CQ;_CK=_CR;return null;}else{var _CS=new T(function(){return B(_CE(_CO));}),_CT=new T(function(){var _CU=(_CN-_CM|0)+1|0;switch(_CU){case -1:return _CM;break;case 0:return E(_ez);break;default:var _CV=function(_){var _CW=E(_Cv)(E(_CO));return new F(function(){return _3R(_CW,0);});};return B(_Cw(B(_4g(_CV)),_CU))+_CM|0;}});return [0,_CT,_CS];}})(_CI,_CJ,_CK);if(_CL!=null){return _CL;}}},_CX=(function(){var ba = window['newByteArr'](16);ba['v']['f64'][0] = Math.random();ba['v']['f64'][1] = Math.random();return window['md51'](ba,16);}),_CY=function(_CZ,_){while(1){var _D0=(function(_D1,_){var _D2=E(_D1);if(!_D2[0]){return _17;}else{var _D3=_D2[2],_D4=E(_D2[1]);if(!_D4[0]){_CZ=_D3;return null;}else{var _D5=_D4[2],_D6=E(_D4[1]),_D7=E(_D6[1]),_D8=E(_D6[2]),_D9=E(_CX),_Da=_D9(),_Db=_Da,_Dc=E(_D8[2]),_Dd=E(_D7[2]);if((_Dc-_Dd|0)<4){var _De=function(_Df,_){var _Dg=E(_Df);if(!_Dg[0]){return new F(function(){return _CY(_D3,_);});}else{var _Dh=_Dg[2],_Di=E(_Dg[1]),_Dj=E(_Di[1]),_Dk=E(_Di[2]),_Dl=_D9(),_Dm=_Dl,_Dn=E(_Dk[2]),_Do=E(_Dj[2]);if((_Dn-_Do|0)<4){var _Dp=B(_De(_Dh,_));return [1,_17,_Dp];}else{var _Dq=B(_De(_Dh,_)),_Dr=new T(function(){return E(B(_CH((_Do+2|0)+1|0,(_Dn-2|0)-1|0,_Dm))[1]);});return [1,[1,[0,_Dj,[0,_Dk[1],_Dr]],[1,[0,[0,_Dj[1],_Dr],_Dk],_17]],_Dq];}}},_Ds=B(_De(_D5,_));return [1,_17,_Ds];}else{var _Dt=function(_Du,_){var _Dv=E(_Du);if(!_Dv[0]){return new F(function(){return _CY(_D3,_);});}else{var _Dw=_Dv[2],_Dx=E(_Dv[1]),_Dy=E(_Dx[1]),_Dz=E(_Dx[2]),_DA=_D9(),_DB=_DA,_DC=E(_Dz[2]),_DD=E(_Dy[2]);if((_DC-_DD|0)<4){var _DE=B(_Dt(_Dw,_));return [1,_17,_DE];}else{var _DF=B(_Dt(_Dw,_)),_DG=new T(function(){return E(B(_CH((_DD+2|0)+1|0,(_DC-2|0)-1|0,_DB))[1]);});return [1,[1,[0,_Dy,[0,_Dz[1],_DG]],[1,[0,[0,_Dy[1],_DG],_Dz],_17]],_DF];}}},_DH=B(_Dt(_D5,_)),_DI=new T(function(){return E(B(_CH((_Dd+2|0)+1|0,(_Dc-2|0)-1|0,_Db))[1]);});return [1,[1,[0,_D7,[0,_D8[1],_DI]],[1,[0,[0,_D7[1],_DI],_D8],_17]],_DH];}}}})(_CZ,_);if(_D0!=null){return _D0;}}},_DJ=function(_DK,_){var _DL=E(_DK);if(!_DL[0]){return _17;}else{var _DM=_DL[2],_DN=E(_DL[1]),_DO=E(_DN[1]),_DP=E(_DN[2]),_DQ=E(_CX),_DR=_DQ(),_DS=_DR,_DT=E(_DP[1]),_DU=E(_DO[1]);if((_DT-_DU|0)<4){var _DV=function(_DW,_){var _DX=E(_DW);if(!_DX[0]){return _17;}else{var _DY=_DX[2],_DZ=E(_DX[1]),_E0=E(_DZ[1]),_E1=E(_DZ[2]),_E2=_DQ(),_E3=_E2,_E4=E(_E1[1]),_E5=E(_E0[1]);if((_E4-_E5|0)<4){var _E6=B(_DV(_DY,_));return [1,_17,_E6];}else{var _E7=B(_DV(_DY,_)),_E8=new T(function(){return E(B(_CH((_E5+2|0)+1|0,(_E4-2|0)-1|0,_E3))[1]);});return [1,[1,[0,_E0,[0,_E8,_E1[2]]],[1,[0,[0,_E8,_E0[2]],_E1],_17]],_E7];}}},_E9=B(_DV(_DM,_));return [1,_17,_E9];}else{var _Ea=function(_Eb,_){var _Ec=E(_Eb);if(!_Ec[0]){return _17;}else{var _Ed=_Ec[2],_Ee=E(_Ec[1]),_Ef=E(_Ee[1]),_Eg=E(_Ee[2]),_Eh=_DQ(),_Ei=_Eh,_Ej=E(_Eg[1]),_Ek=E(_Ef[1]);if((_Ej-_Ek|0)<4){var _El=B(_Ea(_Ed,_));return [1,_17,_El];}else{var _Em=B(_Ea(_Ed,_)),_En=new T(function(){return E(B(_CH((_Ek+2|0)+1|0,(_Ej-2|0)-1|0,_Ei))[1]);});return [1,[1,[0,_Ef,[0,_En,_Eg[2]]],[1,[0,[0,_En,_Ef[2]],_Eg],_17]],_Em];}}},_Eo=B(_Ea(_DM,_)),_Ep=new T(function(){return E(B(_CH((_DU+2|0)+1|0,(_DT-2|0)-1|0,_DS))[1]);});return [1,[1,[0,_DO,[0,_Ep,_DP[2]]],[1,[0,[0,_Ep,_DO[2]],_DP],_17]],_Eo];}}},_Eq=0,_Er=[0,_Eq,_Eq],_Es=34,_Et=44,_Eu=[0,_Et,_Es],_Ev=[0,_Er,_Eu],_Ew=[1,_Ev,_17],_Ex=function(_Ey,_){var _Ez=E(_Ey);if(_Ez==1){var _EA=B(_DJ(_Ew,_)),_EB=B(_CY(_EA,_)),_EC=_EB;return new T(function(){return B(_Ct(_EC));});}else{var _ED=B(_Ex(_Ez+1|0,_)),_EE=B(_DJ(_ED,_)),_EF=B(_CY(_EE,_)),_EG=_EF;return new T(function(){return B(_Ct(_EG));});}},_EH=function(_EI,_){var _EJ=E(_EI);if(!_EJ[0]){return _17;}else{var _EK=_EJ[2],_EL=E(_EJ[1]),_EM=E(_EL[1]),_EN=E(_EL[2]),_EO=E(_CX),_EP=_EO(),_EQ=_EP,_ER=_EO(),_ES=_ER,_ET=_EO(),_EU=_ET,_EV=_EO(),_EW=_EV,_EX=E(_EM[1]),_EY=E(_EN[1]);if((_EX+1|0)>(_EY-2|0)){var _EZ=function(_F0,_){while(1){var _F1=(function(_F2,_){var _F3=E(_F2);if(!_F3[0]){return _17;}else{var _F4=_F3[2],_F5=E(_F3[1]),_F6=E(_F5[1]),_F7=E(_F5[2]),_F8=_EO(),_F9=_F8,_Fa=_EO(),_Fb=_Fa,_Fc=_EO(),_Fd=_Fc,_Fe=_EO(),_Ff=_Fe,_Fg=E(_F6[1]),_Fh=E(_F7[1]);if((_Fg+1|0)>(_Fh-2|0)){_F0=_F4;return null;}else{var _Fi=E(_F6[2]),_Fj=E(_F7[2]);if((_Fi+1|0)>(_Fj-2|0)){_F0=_F4;return null;}else{var _Fk=B(_EZ(_F4,_)),_Fl=new T(function(){return E(B(_CH(_Fg+1|0,_Fh-2|0,_F9))[1]);}),_Fm=new T(function(){return E(B(_CH(_Fi+1|0,_Fj-2|0,_Fd))[1]);}),_Fn=new T(function(){return E(B(_CH((E(_Fm)+2|0)-1|0,_Fj-1|0,_Ff))[1]);}),_Fo=new T(function(){return E(B(_CH((E(_Fl)+2|0)-1|0,_Fh-1|0,_Fb))[1]);});return [1,[0,[0,_Fl,_Fm],[0,_Fo,_Fn]],_Fk];}}}})(_F0,_);if(_F1!=null){return _F1;}}};return new F(function(){return _EZ(_EK,_);});}else{var _Fp=E(_EM[2]),_Fq=E(_EN[2]);if((_Fp+1|0)>(_Fq-2|0)){var _Fr=function(_Fs,_){while(1){var _Ft=(function(_Fu,_){var _Fv=E(_Fu);if(!_Fv[0]){return _17;}else{var _Fw=_Fv[2],_Fx=E(_Fv[1]),_Fy=E(_Fx[1]),_Fz=E(_Fx[2]),_FA=_EO(),_FB=_FA,_FC=_EO(),_FD=_FC,_FE=_EO(),_FF=_FE,_FG=_EO(),_FH=_FG,_FI=E(_Fy[1]),_FJ=E(_Fz[1]);if((_FI+1|0)>(_FJ-2|0)){_Fs=_Fw;return null;}else{var _FK=E(_Fy[2]),_FL=E(_Fz[2]);if((_FK+1|0)>(_FL-2|0)){_Fs=_Fw;return null;}else{var _FM=B(_Fr(_Fw,_)),_FN=new T(function(){return E(B(_CH(_FI+1|0,_FJ-2|0,_FB))[1]);}),_FO=new T(function(){return E(B(_CH(_FK+1|0,_FL-2|0,_FF))[1]);}),_FP=new T(function(){return E(B(_CH((E(_FO)+2|0)-1|0,_FL-1|0,_FH))[1]);}),_FQ=new T(function(){return E(B(_CH((E(_FN)+2|0)-1|0,_FJ-1|0,_FD))[1]);});return [1,[0,[0,_FN,_FO],[0,_FQ,_FP]],_FM];}}}})(_Fs,_);if(_Ft!=null){return _Ft;}}};return new F(function(){return _Fr(_EK,_);});}else{var _FR=function(_FS,_){while(1){var _FT=(function(_FU,_){var _FV=E(_FU);if(!_FV[0]){return _17;}else{var _FW=_FV[2],_FX=E(_FV[1]),_FY=E(_FX[1]),_FZ=E(_FX[2]),_G0=_EO(),_G1=_G0,_G2=_EO(),_G3=_G2,_G4=_EO(),_G5=_G4,_G6=_EO(),_G7=_G6,_G8=E(_FY[1]),_G9=E(_FZ[1]);if((_G8+1|0)>(_G9-2|0)){_FS=_FW;return null;}else{var _Ga=E(_FY[2]),_Gb=E(_FZ[2]);if((_Ga+1|0)>(_Gb-2|0)){_FS=_FW;return null;}else{var _Gc=B(_FR(_FW,_)),_Gd=new T(function(){return E(B(_CH(_G8+1|0,_G9-2|0,_G1))[1]);}),_Ge=new T(function(){return E(B(_CH(_Ga+1|0,_Gb-2|0,_G5))[1]);}),_Gf=new T(function(){return E(B(_CH((E(_Ge)+2|0)-1|0,_Gb-1|0,_G7))[1]);}),_Gg=new T(function(){return E(B(_CH((E(_Gd)+2|0)-1|0,_G9-1|0,_G3))[1]);});return [1,[0,[0,_Gd,_Ge],[0,_Gg,_Gf]],_Gc];}}}})(_FS,_);if(_FT!=null){return _FT;}}},_Gh=B(_FR(_EK,_)),_Gi=new T(function(){return E(B(_CH(_EX+1|0,_EY-2|0,_EQ))[1]);}),_Gj=new T(function(){return E(B(_CH(_Fp+1|0,_Fq-2|0,_EU))[1]);}),_Gk=new T(function(){return E(B(_CH((E(_Gj)+2|0)-1|0,_Fq-1|0,_EW))[1]);}),_Gl=new T(function(){return E(B(_CH((E(_Gi)+2|0)-1|0,_EY-1|0,_ES))[1]);});return [1,[0,[0,_Gi,_Gj],[0,_Gl,_Gk]],_Gh];}}}},_Gm=function(_Gn,_Go,_){var _Gp=E(_Gn);if(!_Gp[0]){return _17;}else{var _Gq=_Gp[2],_Gr=E(_Go);if(!_Gr[0]){return _17;}else{var _Gs=_Gr[2],_Gt=E(_Gp[1]),_Gu=E(_Gt[2]),_Gv=E(_Gr[1]),_Gw=E(_Gv[1]),_Gx=_Gw[1],_Gy=E(_Gv[2])[1],_Gz=E(E(_Gt[1])[2]);if(!E(_Gz)){var _GA=B(_Gm(_Gq,_Gs,_));return [1,_17,_GA];}else{var _GB=E(_CX),_GC=_GB(),_GD=_GC,_GE=function(_GF,_GG,_){var _GH=E(_GF);if(!_GH[0]){return _17;}else{var _GI=_GH[2],_GJ=E(_GG);if(!_GJ[0]){return _17;}else{var _GK=_GJ[2],_GL=E(_GH[1]),_GM=E(_GL[2]),_GN=E(_GJ[1]),_GO=E(_GN[1]),_GP=_GO[1],_GQ=E(_GN[2])[1],_GR=E(E(_GL[1])[2]);if(!E(_GR)){var _GS=B(_GE(_GI,_GK,_));return [1,_17,_GS];}else{var _GT=_GB(),_GU=_GT,_GV=B(_GE(_GI,_GK,_)),_GW=new T(function(){return E(B(_CH(E(_GP),E(_GQ),_GU))[1]);});return [1,[1,[0,[0,[0,_GW,_GR],[0,_GW,_GO[2]]],[0,_GW,_GR]],_17],_GV];}}}},_GX=B(_GE(_Gq,_Gs,_)),_GY=new T(function(){return E(B(_CH(E(_Gx),E(_Gy),_GD))[1]);});return [1,[1,[0,[0,[0,_GY,_Gz],[0,_GY,_Gw[2]]],[0,_GY,_Gz]],_17],_GX];}}}},_GZ=function(_H0,_H1,_){var _H2=E(_H0);if(!_H2[0]){return _17;}else{var _H3=_H2[2],_H4=E(_H1);if(!_H4[0]){return _17;}else{var _H5=_H4[2],_H6=E(_H2[1]),_H7=E(_H6[1]),_H8=E(_H4[1]),_H9=E(_H8[1])[1],_Ha=E(_H8[2]),_Hb=_Ha[1],_Hc=E(E(_H6[2])[2]);if(E(_Hc)==34){var _Hd=B(_GZ(_H3,_H5,_));return [1,_17,_Hd];}else{var _He=E(_CX),_Hf=_He(),_Hg=_Hf,_Hh=function(_Hi,_Hj,_){var _Hk=E(_Hi);if(!_Hk[0]){return _17;}else{var _Hl=_Hk[2],_Hm=E(_Hj);if(!_Hm[0]){return _17;}else{var _Hn=_Hm[2],_Ho=E(_Hk[1]),_Hp=E(_Ho[1]),_Hq=E(_Hm[1]),_Hr=E(_Hq[1])[1],_Hs=E(_Hq[2]),_Ht=_Hs[1],_Hu=E(E(_Ho[2])[2]);if(E(_Hu)==34){var _Hv=B(_Hh(_Hl,_Hn,_));return [1,_17,_Hv];}else{var _Hw=_He(),_Hx=_Hw,_Hy=B(_Hh(_Hl,_Hn,_)),_Hz=new T(function(){return E(B(_CH(E(_Hr),E(_Ht),_Hx))[1]);});return [1,[1,[0,[0,[0,_Hz,_Hs[2]],[0,_Hz,_Hu]],[0,_Hz,_Hu]],_17],_Hy];}}}},_HA=B(_Hh(_H3,_H5,_)),_HB=new T(function(){return E(B(_CH(E(_H9),E(_Hb),_Hg))[1]);});return [1,[1,[0,[0,[0,_HB,_Ha[2]],[0,_HB,_Hc]],[0,_HB,_Hc]],_17],_HA];}}}},_HC=function(_HD,_HE,_){var _HF=E(_HD);if(!_HF[0]){return _17;}else{var _HG=_HF[2],_HH=E(_HE);if(!_HH[0]){return _17;}else{var _HI=_HH[2],_HJ=E(_HF[1]),_HK=E(_HJ[2]),_HL=E(_HH[1]),_HM=E(_HL[1]),_HN=_HM[2],_HO=E(_HL[2])[2],_HP=E(E(_HJ[1])[1]);if(!E(_HP)){var _HQ=B(_HC(_HG,_HI,_));return [1,_17,_HQ];}else{var _HR=E(_CX),_HS=_HR(),_HT=_HS,_HU=function(_HV,_HW,_){var _HX=E(_HV);if(!_HX[0]){return _17;}else{var _HY=_HX[2],_HZ=E(_HW);if(!_HZ[0]){return _17;}else{var _I0=_HZ[2],_I1=E(_HX[1]),_I2=E(_I1[2]),_I3=E(_HZ[1]),_I4=E(_I3[1]),_I5=_I4[2],_I6=E(_I3[2])[2],_I7=E(E(_I1[1])[1]);if(!E(_I7)){var _I8=B(_HU(_HY,_I0,_));return [1,_17,_I8];}else{var _I9=_HR(),_Ia=_I9,_Ib=B(_HU(_HY,_I0,_)),_Ic=new T(function(){return E(B(_CH(E(_I5),E(_I6),_Ia))[1]);});return [1,[1,[0,[0,[0,_I7,_Ic],[0,_I4[1],_Ic]],[0,_I7,_Ic]],_17],_Ib];}}}},_Id=B(_HU(_HG,_HI,_)),_Ie=new T(function(){return E(B(_CH(E(_HN),E(_HO),_HT))[1]);});return [1,[1,[0,[0,[0,_HP,_Ie],[0,_HM[1],_Ie]],[0,_HP,_Ie]],_17],_Id];}}}},_If=function(_Ig,_Ih,_){var _Ii=E(_Ig);if(!_Ii[0]){return _17;}else{var _Ij=_Ii[2],_Ik=E(_Ih);if(!_Ik[0]){return _17;}else{var _Il=_Ik[2],_Im=E(_Ii[1]),_In=E(_Im[1]),_Io=E(_Ik[1]),_Ip=E(_Io[1])[2],_Iq=E(_Io[2]),_Ir=_Iq[2],_Is=E(E(_Im[2])[1]);if(E(_Is)==44){var _It=B(_If(_Ij,_Il,_));return [1,_17,_It];}else{var _Iu=E(_CX),_Iv=_Iu(),_Iw=_Iv,_Ix=function(_Iy,_Iz,_){var _IA=E(_Iy);if(!_IA[0]){return _17;}else{var _IB=_IA[2],_IC=E(_Iz);if(!_IC[0]){return _17;}else{var _ID=_IC[2],_IE=E(_IA[1]),_IF=E(_IE[1]),_IG=E(_IC[1]),_IH=E(_IG[1])[2],_II=E(_IG[2]),_IJ=_II[2],_IK=E(E(_IE[2])[1]);if(E(_IK)==44){var _IL=B(_Ix(_IB,_ID,_));return [1,_17,_IL];}else{var _IM=_Iu(),_IN=_IM,_IO=B(_Ix(_IB,_ID,_)),_IP=new T(function(){return E(B(_CH(E(_IH),E(_IJ),_IN))[1]);});return [1,[1,[0,[0,[0,_II[1],_IP],[0,_IK,_IP]],[0,_IK,_IP]],_17],_IO];}}}},_IQ=B(_Ix(_Ij,_Il,_)),_IR=new T(function(){return E(B(_CH(E(_Ip),E(_Ir),_Iw))[1]);});return [1,[1,[0,[0,[0,_Iq[1],_IR],[0,_Is,_IR]],[0,_Is,_IR]],_17],_IQ];}}}},_IS=function(_IT,_IU){return [0,1,E(_IT),_IU,E(_vq),E(_vq)];},_IV=function(_IW,_IX,_IY){var _IZ=E(_IY);if(!_IZ[0]){return new F(function(){return _we(_IZ[2],_IZ[3],_IZ[4],B(_IV(_IW,_IX,_IZ[5])));});}else{return new F(function(){return _IS(_IW,_IX);});}},_J0=function(_J1,_J2,_J3){var _J4=E(_J3);if(!_J4[0]){return new F(function(){return _vv(_J4[2],_J4[3],B(_J0(_J1,_J2,_J4[4])),_J4[5]);});}else{return new F(function(){return _IS(_J1,_J2);});}},_J5=function(_J6,_J7,_J8,_J9,_Ja,_Jb,_Jc){return new F(function(){return _vv(_J9,_Ja,B(_J0(_J6,_J7,_Jb)),_Jc);});},_Jd=function(_Je,_Jf,_Jg,_Jh,_Ji,_Jj,_Jk,_Jl){var _Jm=E(_Jg);if(!_Jm[0]){var _Jn=_Jm[1],_Jo=_Jm[2],_Jp=_Jm[3],_Jq=_Jm[4],_Jr=_Jm[5];if((imul(3,_Jn)|0)>=_Jh){if((imul(3,_Jh)|0)>=_Jn){return [0,(_Jn+_Jh|0)+1|0,E(_Je),_Jf,E(_Jm),[0,_Jh,E(_Ji),_Jj,E(_Jk),E(_Jl)]];}else{return new F(function(){return _we(_Jo,_Jp,_Jq,B(_Jd(_Je,_Jf,_Jr,_Jh,_Ji,_Jj,_Jk,_Jl)));});}}else{return new F(function(){return _vv(_Ji,_Jj,B(_Js(_Je,_Jf,_Jn,_Jo,_Jp,_Jq,_Jr,_Jk)),_Jl);});}}else{return new F(function(){return _J5(_Je,_Jf,_Jh,_Ji,_Jj,_Jk,_Jl);});}},_Js=function(_Jt,_Ju,_Jv,_Jw,_Jx,_Jy,_Jz,_JA){var _JB=E(_JA);if(!_JB[0]){var _JC=_JB[1],_JD=_JB[2],_JE=_JB[3],_JF=_JB[4],_JG=_JB[5];if((imul(3,_Jv)|0)>=_JC){if((imul(3,_JC)|0)>=_Jv){return [0,(_Jv+_JC|0)+1|0,E(_Jt),_Ju,[0,_Jv,E(_Jw),_Jx,E(_Jy),E(_Jz)],E(_JB)];}else{return new F(function(){return _we(_Jw,_Jx,_Jy,B(_Jd(_Jt,_Ju,_Jz,_JC,_JD,_JE,_JF,_JG)));});}}else{return new F(function(){return _vv(_JD,_JE,B(_Js(_Jt,_Ju,_Jv,_Jw,_Jx,_Jy,_Jz,_JF)),_JG);});}}else{return new F(function(){return _IV(_Jt,_Ju,[0,_Jv,E(_Jw),_Jx,E(_Jy),E(_Jz)]);});}},_JH=function(_JI,_JJ,_JK,_JL){var _JM=E(_JK);if(!_JM[0]){var _JN=_JM[1],_JO=_JM[2],_JP=_JM[3],_JQ=_JM[4],_JR=_JM[5],_JS=E(_JL);if(!_JS[0]){var _JT=_JS[1],_JU=_JS[2],_JV=_JS[3],_JW=_JS[4],_JX=_JS[5];if((imul(3,_JN)|0)>=_JT){if((imul(3,_JT)|0)>=_JN){return [0,(_JN+_JT|0)+1|0,E(_JI),_JJ,E(_JM),E(_JS)];}else{return new F(function(){return _we(_JO,_JP,_JQ,B(_Jd(_JI,_JJ,_JR,_JT,_JU,_JV,_JW,_JX)));});}}else{return new F(function(){return _vv(_JU,_JV,B(_Js(_JI,_JJ,_JN,_JO,_JP,_JQ,_JR,_JW)),_JX);});}}else{return new F(function(){return _IV(_JI,_JJ,_JM);});}}else{return new F(function(){return _J0(_JI,_JJ,_JL);});}},_JY=function(_JZ,_K0,_K1,_K2,_K3){var _K4=E(_JZ);if(_K4==1){var _K5=E(_K3);if(!_K5[0]){return [0,[0,1,[0,_K0,_K1],_K2,E(_vq),E(_vq)],_17,_17];}else{var _K6=E(E(_K5[1])[1]),_K7=E(_K6[1]);return (_K0>=_K7)?(_K0!=_K7)?[0,[0,1,[0,_K0,_K1],_K2,E(_vq),E(_vq)],_17,_K5]:(_K1<E(_K6[2]))?[0,[0,1,[0,_K0,_K1],_K2,E(_vq),E(_vq)],_K5,_17]:[0,[0,1,[0,_K0,_K1],_K2,E(_vq),E(_vq)],_17,_K5]:[0,[0,1,[0,_K0,_K1],_K2,E(_vq),E(_vq)],_K5,_17];}}else{var _K8=B(_JY(_K4>>1,_K0,_K1,_K2,_K3)),_K9=_K8[1],_Ka=_K8[3],_Kb=E(_K8[2]);if(!_Kb[0]){return [0,_K9,_17,_Ka];}else{var _Kc=E(_Kb[1]),_Kd=_Kc[1],_Ke=_Kc[2],_Kf=E(_Kb[2]);if(!_Kf[0]){var _Kg=new T(function(){return B(_IV(_Kd,_Ke,_K9));});return [0,_Kg,_17,_Ka];}else{var _Kh=_Kf[2],_Ki=E(_Kf[1]),_Kj=_Ki[2],_Kk=E(_Kd),_Kl=E(_Ki[1]),_Km=_Kl[2],_Kn=E(_Kk[1]),_Ko=E(_Kl[1]);if(_Kn>=_Ko){if(_Kn!=_Ko){return [0,_K9,_17,_Kb];}else{var _Kp=E(_Km);if(E(_Kk[2])<_Kp){var _Kq=B(_JY(_K4>>1,_Ko,_Kp,_Kj,_Kh)),_Kr=_Kq[1],_Ks=new T(function(){return B(_JH(_Kk,_Ke,_K9,_Kr));});return [0,_Ks,_Kq[2],_Kq[3]];}else{return [0,_K9,_17,_Kb];}}}else{var _Kt=B(_Ku(_K4>>1,_Ko,_Km,_Kj,_Kh)),_Kv=_Kt[1],_Kw=new T(function(){return B(_JH(_Kk,_Ke,_K9,_Kv));});return [0,_Kw,_Kt[2],_Kt[3]];}}}}},_Ku=function(_Kx,_Ky,_Kz,_KA,_KB){var _KC=E(_Kx);if(_KC==1){var _KD=E(_KB);if(!_KD[0]){return [0,[0,1,[0,_Ky,_Kz],_KA,E(_vq),E(_vq)],_17,_17];}else{var _KE=E(E(_KD[1])[1]),_KF=E(_KE[1]);if(_Ky>=_KF){if(_Ky!=_KF){return [0,[0,1,[0,_Ky,_Kz],_KA,E(_vq),E(_vq)],_17,_KD];}else{var _KG=E(_Kz);return (_KG<E(_KE[2]))?[0,[0,1,[0,_Ky,_KG],_KA,E(_vq),E(_vq)],_KD,_17]:[0,[0,1,[0,_Ky,_KG],_KA,E(_vq),E(_vq)],_17,_KD];}}else{return [0,[0,1,[0,_Ky,_Kz],_KA,E(_vq),E(_vq)],_KD,_17];}}}else{var _KH=B(_Ku(_KC>>1,_Ky,_Kz,_KA,_KB)),_KI=_KH[1],_KJ=_KH[3],_KK=E(_KH[2]);if(!_KK[0]){return [0,_KI,_17,_KJ];}else{var _KL=E(_KK[1]),_KM=_KL[1],_KN=_KL[2],_KO=E(_KK[2]);if(!_KO[0]){var _KP=new T(function(){return B(_IV(_KM,_KN,_KI));});return [0,_KP,_17,_KJ];}else{var _KQ=_KO[2],_KR=E(_KO[1]),_KS=_KR[2],_KT=E(_KM),_KU=E(_KR[1]),_KV=_KU[2],_KW=E(_KT[1]),_KX=E(_KU[1]);if(_KW>=_KX){if(_KW!=_KX){return [0,_KI,_17,_KK];}else{var _KY=E(_KV);if(E(_KT[2])<_KY){var _KZ=B(_JY(_KC>>1,_KX,_KY,_KS,_KQ)),_L0=_KZ[1],_L1=new T(function(){return B(_JH(_KT,_KN,_KI,_L0));});return [0,_L1,_KZ[2],_KZ[3]];}else{return [0,_KI,_17,_KK];}}}else{var _L2=B(_Ku(_KC>>1,_KX,_KV,_KS,_KQ)),_L3=_L2[1],_L4=new T(function(){return B(_JH(_KT,_KN,_KI,_L3));});return [0,_L4,_L2[2],_L2[3]];}}}}},_L5=function(_L6,_L7){while(1){var _L8=E(_L7);if(!_L8[0]){return E(_L6);}else{var _L9=E(_L8[1]),_La=E(_L9[1]),_Lb=B(_Ca(_La[1],_La[2],_L9[2],_L6));_L7=_L8[2];_L6=_Lb;continue;}}},_Lc=function(_Ld,_Le,_Lf,_Lg,_Lh){return new F(function(){return _L5(B(_Ca(_Le,_Lf,_Lg,_Ld)),_Lh);});},_Li=function(_Lj,_Lk,_Ll){var _Lm=E(_Lk),_Ln=E(_Lm[1]);return new F(function(){return _L5(B(_Ca(_Ln[1],_Ln[2],_Lm[2],_Lj)),_Ll);});},_Lo=function(_Lp,_Lq,_Lr){var _Ls=E(_Lr);if(!_Ls[0]){return E(_Lq);}else{var _Lt=E(_Ls[1]),_Lu=_Lt[1],_Lv=_Lt[2],_Lw=E(_Ls[2]);if(!_Lw[0]){return new F(function(){return _IV(_Lu,_Lv,_Lq);});}else{var _Lx=_Lw[2],_Ly=E(_Lw[1]),_Lz=_Ly[2],_LA=E(_Lu),_LB=_LA[2],_LC=E(_Ly[1]),_LD=_LC[2],_LE=E(_LA[1]),_LF=E(_LC[1]),_LG=function(_LH){var _LI=B(_Ku(_Lp,_LF,_LD,_Lz,_Lx)),_LJ=_LI[1],_LK=E(_LI[3]);if(!_LK[0]){return new F(function(){return _Lo(_Lp<<1,B(_JH(_LA,_Lv,_Lq,_LJ)),_LI[2]);});}else{return new F(function(){return _Li(B(_JH(_LA,_Lv,_Lq,_LJ)),_LK[1],_LK[2]);});}};if(_LE>=_LF){if(_LE!=_LF){return new F(function(){return _Lc(_Lq,_LE,_LB,_Lv,_Lw);});}else{var _LL=E(_LB);if(_LL<E(_LD)){return new F(function(){return _LG(_);});}else{return new F(function(){return _Lc(_Lq,_LE,_LL,_Lv,_Lw);});}}}else{return new F(function(){return _LG(_);});}}}},_LM=function(_LN,_LO,_LP,_LQ,_LR,_LS){var _LT=E(_LS);if(!_LT[0]){return new F(function(){return _IV([0,_LP,_LQ],_LR,_LO);});}else{var _LU=_LT[2],_LV=E(_LT[1]),_LW=_LV[2],_LX=E(_LV[1]),_LY=_LX[2],_LZ=E(_LX[1]),_M0=function(_M1){var _M2=B(_Ku(_LN,_LZ,_LY,_LW,_LU)),_M3=_M2[1],_M4=E(_M2[3]);if(!_M4[0]){return new F(function(){return _Lo(_LN<<1,B(_JH([0,_LP,_LQ],_LR,_LO,_M3)),_M2[2]);});}else{return new F(function(){return _Li(B(_JH([0,_LP,_LQ],_LR,_LO,_M3)),_M4[1],_M4[2]);});}};if(_LP>=_LZ){if(_LP!=_LZ){return new F(function(){return _Lc(_LO,_LP,_LQ,_LR,_LT);});}else{if(_LQ<E(_LY)){return new F(function(){return _M0(_);});}else{return new F(function(){return _Lc(_LO,_LP,_LQ,_LR,_LT);});}}}else{return new F(function(){return _M0(_);});}}},_M5=function(_M6,_M7,_M8,_M9,_Ma,_Mb){var _Mc=E(_Mb);if(!_Mc[0]){return new F(function(){return _IV([0,_M8,_M9],_Ma,_M7);});}else{var _Md=_Mc[2],_Me=E(_Mc[1]),_Mf=_Me[2],_Mg=E(_Me[1]),_Mh=_Mg[2],_Mi=E(_Mg[1]),_Mj=function(_Mk){var _Ml=B(_Ku(_M6,_Mi,_Mh,_Mf,_Md)),_Mm=_Ml[1],_Mn=E(_Ml[3]);if(!_Mn[0]){return new F(function(){return _Lo(_M6<<1,B(_JH([0,_M8,_M9],_Ma,_M7,_Mm)),_Ml[2]);});}else{return new F(function(){return _Li(B(_JH([0,_M8,_M9],_Ma,_M7,_Mm)),_Mn[1],_Mn[2]);});}};if(_M8>=_Mi){if(_M8!=_Mi){return new F(function(){return _Lc(_M7,_M8,_M9,_Ma,_Mc);});}else{var _Mo=E(_M9);if(_Mo<E(_Mh)){return new F(function(){return _Mj(_);});}else{return new F(function(){return _Lc(_M7,_M8,_Mo,_Ma,_Mc);});}}}else{return new F(function(){return _Mj(_);});}}},_Mp=function(_Mq){var _Mr=E(_Mq);if(!_Mr[0]){return [1];}else{var _Ms=E(_Mr[1]),_Mt=_Ms[1],_Mu=_Ms[2],_Mv=E(_Mr[2]);if(!_Mv[0]){return [0,1,E(_Mt),_Mu,E(_vq),E(_vq)];}else{var _Mw=_Mv[2],_Mx=E(_Mv[1]),_My=_Mx[2],_Mz=E(_Mt),_MA=E(_Mx[1]),_MB=_MA[2],_MC=E(_Mz[1]),_MD=E(_MA[1]);if(_MC>=_MD){if(_MC!=_MD){return new F(function(){return _Lc([0,1,E(_Mz),_Mu,E(_vq),E(_vq)],_MD,_MB,_My,_Mw);});}else{var _ME=E(_MB);if(E(_Mz[2])<_ME){return new F(function(){return _LM(1,[0,1,E(_Mz),_Mu,E(_vq),E(_vq)],_MD,_ME,_My,_Mw);});}else{return new F(function(){return _Lc([0,1,E(_Mz),_Mu,E(_vq),E(_vq)],_MD,_ME,_My,_Mw);});}}}else{return new F(function(){return _M5(1,[0,1,E(_Mz),_Mu,E(_vq),E(_vq)],_MD,_MB,_My,_Mw);});}}}},_MF=new T(function(){return B(_uB(0,34));}),_MG=function(_MH){var _MI=_MH,_MJ=new T(function(){var _MK=E(_MH);if(_MK==44){return [0];}else{return B(_MG(_MK+1|0));}}),_ML=function(_MM){var _MN=E(_MM);if(!_MN[0]){return E(_MJ);}else{var _MO=_MN[2],_MP=new T(function(){return B(_ML(_MO));});return [1,[0,_MI,_MN[1]],_MP];}};return new F(function(){return _ML(_MF);});},_MQ=new T(function(){return B(_MG(0));}),_MR=32,_MS=new T(function(){return [1,_MR,_MS];}),_MT=function(_MU,_MV){var _MW=E(_MU);if(!_MW[0]){return [0];}else{var _MX=_MW[2],_MY=E(_MV);if(!_MY[0]){return [0];}else{var _MZ=_MY[2],_N0=new T(function(){return B(_MT(_MX,_MZ));});return [1,[0,_MW[1],_MY[1]],_N0];}}},_N1=new T(function(){return B(_MT(_MQ,_MS));}),_N2=new T(function(){return B(_Mp(_N1));}),_N3=35,_N4=function(_N5){return E(E(_N5)[1]);},_N6=function(_N7,_N8,_N9){while(1){var _Na=E(_N9);if(!_Na[0]){return false;}else{if(!B(A(_N4,[_N7,_N8,_Na[1]]))){_N9=_Na[2];continue;}else{return true;}}}},_Nb=function(_Nc){return E(E(_Nc)[1]);},_Nd=function(_Ne){var _Nf=E(_Ne);if(!_Nf[0]){return [0];}else{var _Ng=_Nf[2],_Nh=new T(function(){return B(_Nd(_Ng));},1);return new F(function(){return _1t(_Nf[1],_Nh);});}},_Ni=function(_Nj){return new F(function(){return _k0("Dungeon.hs:(127,5)-(128,21)|function tup");});},_Nk=new T(function(){return B(_Ni(_));}),_Nl=function(_Nm){var _Nn=E(_Nm);if(!_Nn[0]){return E(_Nk);}else{var _No=_Nn[1],_Np=E(_Nn[2]);return (_Np[0]==0)?[0,_No,_No]:(E(_Np[2])[0]==0)?[0,_No,_Np[1]]:E(_Nk);}},_Nq=function(_Nr,_Ns){return new F(function(){return _a6(E(E(_Nr)[2]),E(E(_Ns)[2]));});},_Nt=function(_Nu){var _Nv=E(_Nu);if(!_Nv[0]){return [0];}else{var _Nw=_Nv[2],_Nx=new T(function(){return B(_Nt(_Nw));}),_Ny=function(_Nz){var _NA=E(_Nz);if(!_NA[0]){return E(_Nx);}else{var _NB=_NA[1],_NC=_NA[2],_ND=new T(function(){return B(_Ny(_NC));}),_NE=new T(function(){return B(_Nl(_NB));});return [1,_NE,_ND];}};return new F(function(){return _Ny(B(_C1(2,B(_cp(_Nq,_Nv[1])))));});}},_NF=function(_NG,_NH){var _NI=E(_NH);if(!_NI[0]){return [0];}else{var _NJ=_NI[1],_NK=_NI[2],_NL=new T(function(){var _NM=new T(function(){return B(A(_NG,[_NJ]));}),_NN=B(_jA(_NM,_NK));return [0,_NN[1],_NN[2]];}),_NO=new T(function(){return B(_NF(_NG,E(_NL)[2]));}),_NP=new T(function(){return E(E(_NL)[1]);});return [1,[1,_NJ,_NP],_NO];}},_NQ=function(_NR,_NS){return E(E(_NR)[1])==E(E(_NS)[1]);},_NT=function(_NU,_NV){return new F(function(){return _a6(E(E(_NU)[1]),E(E(_NV)[1]));});},_NW=45,_NX=function(_NY,_NZ){return E(E(_NY)[2])==E(E(_NZ)[2]);},_O0=function(_O1,_O2,_O3,_O4){var _O5=E(_O4);if(!_O5[0]){var _O6=_O5[3],_O7=_O5[4],_O8=_O5[5],_O9=E(_O5[2]),_Oa=E(_O9[1]);if(_O1>=_Oa){if(_O1!=_Oa){return new F(function(){return _we(_O9,_O6,_O7,B(_O0(_O1,_O2,_O3,_O8)));});}else{var _Ob=E(_O9[2]);if(_O2>=_Ob){if(_O2!=_Ob){return new F(function(){return _we(_O9,_O6,_O7,B(_O0(_O1,_O2,_O3,_O8)));});}else{return [0,_O5[1],[0,_O1,_O2],_O3,E(_O7),E(_O8)];}}else{return new F(function(){return _vv(_O9,_O6,B(_O0(_O1,_O2,_O3,_O7)),_O8);});}}}else{return new F(function(){return _vv(_O9,_O6,B(_O0(_O1,_O2,_O3,_O7)),_O8);});}}else{return [0,1,[0,_O1,_O2],_O3,E(_vq),E(_vq)];}},_Oc=function(_Od,_Oe,_Of,_Og){var _Oh=E(_Og);if(!_Oh[0]){var _Oi=_Oh[3],_Oj=_Oh[4],_Ok=_Oh[5],_Ol=E(_Oh[2]),_Om=E(_Ol[1]);if(_Od>=_Om){if(_Od!=_Om){return new F(function(){return _we(_Ol,_Oi,_Oj,B(_Oc(_Od,_Oe,_Of,_Ok)));});}else{var _On=E(_Oe),_Oo=E(_Ol[2]);if(_On>=_Oo){if(_On!=_Oo){return new F(function(){return _we(_Ol,_Oi,_Oj,B(_O0(_Od,_On,_Of,_Ok)));});}else{return [0,_Oh[1],[0,_Od,_On],_Of,E(_Oj),E(_Ok)];}}else{return new F(function(){return _vv(_Ol,_Oi,B(_O0(_Od,_On,_Of,_Oj)),_Ok);});}}}else{return new F(function(){return _vv(_Ol,_Oi,B(_Oc(_Od,_Oe,_Of,_Oj)),_Ok);});}}else{return [0,1,[0,_Od,_Oe],_Of,E(_vq),E(_vq)];}},_Op=function(_Oq,_Or,_Os){var _Ot=new T(function(){return [1,_Oq,_Ot];}),_Ou=function(_Ov){var _Ow=E(_Ov);if(!_Ow[0]){return E(_Os);}else{var _Ox=E(_Ow[1]),_Oy=E(_Ox[1]),_Oz=E(_Ox[2]),_OA=E(_Oy[1]),_OB=E(_Oz[1]),_OC=B(_Ou(_Ow[2]));if(_OA<=_OB){var _OD=B(_uB(E(_Oy[2]),E(_Oz[2]))),_OE=function(_OF,_OG){var _OH=new T(function(){return _OF==_OB;}),_OI=function(_OJ,_OK){var _OL=E(_OJ);if(!_OL[0]){if(!E(_OH)){return new F(function(){return _OE(_OF+1|0,_OK);});}else{return E(_OC);}}else{var _OM=E(_OK);if(!_OM[0]){return E(_OC);}else{return new F(function(){return _Oc(_OF,_OL[1],_OM[1],B(_OI(_OL[2],_OM[2])));});}}};return new F(function(){return _OI(_OD,_OG);});};return new F(function(){return _OE(_OA,_Ot);});}else{return E(_OC);}}};return new F(function(){return _Ou(_Or);});},_ON=function(_OO){return E(E(_OO)[2]);},_OP=function(_){var _OQ=B(_Ex(0,_)),_OR=B(_EH(_OQ,_)),_OS=_OR,_OT=B(_Gm(_OQ,_OS,_)),_OU=_OT,_OV=B(_GZ(_OQ,_OS,_)),_OW=_OV,_OX=B(_HC(_OQ,_OS,_)),_OY=_OX,_OZ=B(_If(_OQ,_OS,_)),_P0=_OZ;return new T(function(){var _P1=new T(function(){var _P2=new T(function(){var _P3=new T(function(){return B(_Nd(_P0));}),_P4=function(_P5){var _P6=E(_P5);if(!_P6[0]){return E(_P3);}else{var _P7=_P6[2],_P8=new T(function(){return B(_P4(_P7));},1);return new F(function(){return _1t(_P6[1],_P8);});}};return B(_P4(_OY));}),_P9=function(_Pa){var _Pb=E(_Pa);if(!_Pb[0]){return E(_P2);}else{var _Pc=_Pb[2],_Pd=new T(function(){return B(_P9(_Pc));},1);return new F(function(){return _1t(_Pb[1],_Pd);});}};return B(_P9(_OW));}),_Pe=function(_Pf){var _Pg=E(_Pf);if(!_Pg[0]){return E(_P1);}else{var _Ph=_Pg[2],_Pi=new T(function(){return B(_Pe(_Ph));},1);return new F(function(){return _1t(_Pg[1],_Pi);});}},_Pj=B(_Pe(_OU)),_Pk=B(_uV(_Nb,_Pj)),_Pl=new T(function(){return B(_uV(_ON,_Pj));}),_Pm=new T(function(){var _Pn=function(_Po){while(1){var _Pp=(function(_Pq){var _Pr=E(_Pq);if(!_Pr[0]){return [0];}else{var _Ps=_Pr[2],_Pt=E(_Pr[1]),_Pu=E(_Pt[1]),_Pv=E(_Pt[2]);if(E(_Pu[2])!=E(_Pv[2])){_Po=_Ps;return null;}else{var _Pw=new T(function(){return B(_Pn(_Ps));}),_Px=new T(function(){if(!B(_N6(_lV,_Pu,_Pl))){return E(_Pv);}else{return E(_Pu);}});return [1,_Px,_Pw];}}})(_Po);if(_Pp!=null){return _Pp;}}};return B(_Nt(B(_NF(_NQ,B(_cp(_NT,B(_Pn(_Pk))))))));}),_Py=function(_Pz){var _PA=E(_Pz);if(!_PA[0]){return E(_Pm);}else{var _PB=_PA[2],_PC=new T(function(){return B(_Py(_PB));}),_PD=function(_PE){var _PF=E(_PE);if(!_PF[0]){return E(_PC);}else{var _PG=_PF[1],_PH=_PF[2],_PI=new T(function(){return B(_PD(_PH));}),_PJ=new T(function(){return B(_Nl(_PG));});return [1,_PJ,_PI];}};return new F(function(){return _PD(B(_C1(2,B(_cp(_NT,_PA[1])))));});}},_PK=function(_PL){while(1){var _PM=(function(_PN){var _PO=E(_PN);if(!_PO[0]){return [0];}else{var _PP=_PO[2],_PQ=E(_PO[1]),_PR=E(_PQ[1]),_PS=E(_PQ[2]);if(E(_PR[1])!=E(_PS[1])){_PL=_PP;return null;}else{var _PT=new T(function(){return B(_PK(_PP));}),_PU=new T(function(){if(!B(_N6(_lV,_PR,_Pl))){return E(_PS);}else{return E(_PR);}});return [1,_PU,_PT];}}})(_PL);if(_PM!=null){return _PM;}}},_PV=B(_Op(_N3,_OS,B(_Op(_NW,_Pk,B(_Op(_NW,B(_Py(B(_NF(_NX,B(_cp(_Nq,B(_PK(_Pk)))))))),_N2)))))),_PW=function(_PX){var _PY=E(_PX);if(!_PY[0]){return E(_PV);}else{var _PZ=_PY[2],_Q0=E(_PY[1]),_Q1=E(_Q0[1]),_Q2=E(_Q0[2]);if(!B(_N6(_lV,_Q1,_Pl))){return new F(function(){return _Ca(_Q1[1],_Q1[2],_N3,B(_PW(_PZ)));});}else{return new F(function(){return _Ca(_Q2[1],_Q2[2],_N3,B(_PW(_PZ)));});}}};return B(_PW(_Pk));});},_Q3=function(_Q4,_Q5){return new F(function(){return _6W(_Q4,E(_Q5));});},_Q6=function(_Q7,_Q8){while(1){var _Q9=E(_Q7);if(!_Q9[0]){return E(_Q8);}else{_Q7=_Q9[2];var _Qa=_Q8+1|0;_Q8=_Qa;continue;}}},_Qb=new T(function(){return B(unCStr("Map.!: given key is not an element in the map"));}),_Qc=new T(function(){return B(err(_Qb));}),_Qd=function(_Qe,_Qf,_Qg){while(1){var _Qh=E(_Qg);if(!_Qh[0]){var _Qi=_Qh[4],_Qj=_Qh[5],_Qk=E(_Qh[2]),_Ql=E(_Qk[1]);if(_Qe>=_Ql){if(_Qe!=_Ql){_Qg=_Qj;continue;}else{var _Qm=E(_Qk[2]);if(_Qf>=_Qm){if(_Qf!=_Qm){_Qg=_Qj;continue;}else{return E(_Qh[3]);}}else{_Qg=_Qi;continue;}}}else{_Qg=_Qi;continue;}}else{return E(_Qc);}}},_Qn=function(_Qo,_Qp,_Qq){while(1){var _Qr=E(_Qq);if(!_Qr[0]){var _Qs=_Qr[4],_Qt=_Qr[5],_Qu=E(_Qr[2]),_Qv=E(_Qu[1]);if(_Qo>=_Qv){if(_Qo!=_Qv){_Qq=_Qt;continue;}else{var _Qw=E(_Qp),_Qx=E(_Qu[2]);if(_Qw>=_Qx){if(_Qw!=_Qx){return new F(function(){return _Qd(_Qo,_Qw,_Qt);});}else{return E(_Qr[3]);}}else{return new F(function(){return _Qd(_Qo,_Qw,_Qs);});}}}else{_Qq=_Qs;continue;}}else{return E(_Qc);}}},_Qy=new T(function(){return B(_uB(0,20));}),_Qz=function(_QA,_){var _QB=E(_CX)(),_QC=_QB;return new T(function(){var _QD=function(_QE){var _QF=E(_QE);if(!_QF[0]){return [0];}else{var _QG=_QF[2],_QH=new T(function(){return B(_QD(_QG));}),_QI=E(_Qy);if(!_QI[0]){return E(_QH);}else{var _QJ=_QI[1],_QK=_QI[2],_QL=E(_QF[1]),_QM=_QL;if(E(B(_Qn(_QM,_QJ,_QA)))==35){var _QN=new T(function(){var _QO=function(_QP){while(1){var _QQ=(function(_QR){var _QS=E(_QR);if(!_QS[0]){return E(_QH);}else{var _QT=_QS[1],_QU=_QS[2];if(E(B(_Qn(_QM,_QT,_QA)))==35){var _QV=new T(function(){return B(_QO(_QU));});return [1,[0,_QL,_QT],_QV];}else{_QP=_QU;return null;}}})(_QP);if(_QQ!=null){return _QQ;}}};return B(_QO(_QK));});return [1,[0,_QL,_QJ],_QN];}else{var _QW=function(_QX){while(1){var _QY=(function(_QZ){var _R0=E(_QZ);if(!_R0[0]){return E(_QH);}else{var _R1=_R0[1],_R2=_R0[2];if(E(B(_Qn(_QM,_R1,_QA)))==35){var _R3=new T(function(){return B(_QW(_R2));});return [1,[0,_QL,_R1],_R3];}else{_QX=_R2;return null;}}})(_QX);if(_QY!=null){return _QY;}}};return new F(function(){return _QW(_QK);});}}}},_R4=B(_QD(_Qy));return B(_Q3(_R4,B(_CH(0,B(_Q6(_R4,0))-1|0,_QC))[1]));});},_R5=function(_R6){var _R7=new T(function(){var _R8=E(_R6);if(_R8==255){return [0];}else{var _R9=B(_R5(_R8+1|0));return [1,_R9[1],_R9[2]];}});return [0,[0,_R6,_Bz],_R7];},_Ra=[2],_Rb=function(_Rc,_Rd){while(1){var _Re=E(_Rd);if(!_Re[0]){return E(_Rc);}else{var _Rf=E(_Re[1]),_Rg=B(_B7(E(_Rf[1]),_Rf[2],_Rc));_Rd=_Re[2];_Rc=_Rg;continue;}}},_Rh=new T(function(){var _Ri=B(_R5(0));return B(_Rb(_Ra,[1,_Ri[1],_Ri[2]]));}),_Rj=5000,_Rk=1,_Rl=30,_Rm=40,_Rn=10,_Ro=20,_Rp=new T(function(){return B(unCStr("\u30c7\u30d3\u30eb\u30a8\u30f3\u30da\u30e9\u30fc"));}),_Rq=0,_Rr=[1,_Rq,_17],_Rs=[1,_Rq,_Rr],_Rt=[1,_Rq,_Rs],_Ru=new T(function(){return B(_Q6(_Rt,0));}),_Rv=new T(function(){return B(_uB(0,2147483647));}),_Rw=new T(function(){return B(_MT(_Rv,_Rt));}),_Rx=new T(function(){return B(_Rb(_Ra,_Rw));}),_Ry=[0,_ar,_Ru,_Rx],_Rz=[0,_Rp,_Ro,_Ro,_Ro,_Rn,_Rm,_Rl,_Rk,_Rj,_Rj,_Rm,_Rm,_Ry],_RA=[1,_Rz,_17],_RB=150,_RC=60,_RD=85,_RE=50,_RF=1,_RG=[1,_RF,_Rs],_RH=new T(function(){return B(_MT(_Rv,_RG));}),_RI=new T(function(){return B(_Rb(_Ra,_RH));}),_RJ=new T(function(){return B(_Q6(_RG,0));}),_RK=[0,_ar,_RJ,_RI],_RL=new T(function(){return B(unCStr("\u885b\u5175"));}),_RM=[0,_RL,_RD,_RE,_Rm,_RC,_Rl,_Rn,_Rk,_RB,_RB,_Rl,_Rl,_RK],_RN=[1,_RM,_17],_RO=[1,_RF,_17],_RP=[1,_Rq,_RO],_RQ=[1,_Rq,_RP],_RR=new T(function(){return B(_MT(_Rv,_RQ));}),_RS=new T(function(){return B(_Rb(_Ra,_RR));}),_RT=new T(function(){return B(_Q6(_RQ,0));}),_RU=[0,_ar,_RT,_RS],_RV=new T(function(){return B(unCStr("\u72c2\u4eba"));}),_RW=[0,_RV,_RD,_ar,_ar,_Rl,_Rn,_RC,_Rk,_RB,_RB,_ar,_ar,_RU],_RX=[1,_RW,_RN],_RY=[1,_RF,_Rr],_RZ=[1,_Rq,_RY],_S0=new T(function(){return B(_MT(_Rv,_RZ));}),_S1=new T(function(){return B(_Rb(_Ra,_S0));}),_S2=new T(function(){return B(_Q6(_RZ,0));}),_S3=[0,_ar,_S2,_S1],_S4=new T(function(){return B(unCStr("\u30d7\u30ea\u30f3\u30bb\u30b9"));}),_S5=100,_S6=65,_S7=80,_S8=[0,_S4,_Rn,_S7,_S6,_Rm,_RE,_Ro,_Rk,_S5,_S5,_S5,_S5,_S3],_S9=[1,_S8,_RX],_Sa=[0,_S9,_RA,_uw],_Sb=46,_Sc=new T(function(){return [1,_Sb,_Sc];}),_Sd=new T(function(){return B(_MT(_MQ,_Sc));}),_Se=new T(function(){return B(_Mp(_Sd));}),_Sf=(function(e,c) {return e.classList.contains(c);}),_Sg=new T(function(){return B(unCStr("active"));}),_Sh=function(_){var _Si=B(_OP(_)),_Sj=B(_Qz(_Si,_)),_Sk=nMV([0,_Rh,_Sj,_Sj,_Si,_Se,_uw,_By,_Sa]),_Sl=_Sk,_Sm=rMV(_Sl),_Sn=_Sl,_So=function(_Sp,_){var _Sq=rMV(_Sl),_Sr=_Sq,_Ss=new T(function(){var _St=E(_Sr),_Su=_St[1],_Sv=new T(function(){return B(_B7(E(_Sp)[1],_BC,_Su));});return [0,_Sv,_St[2],_St[3],_St[4],_St[5],_St[6],_St[7],_St[8]];}),_=wMV(_Sl,_Ss),_Sw=E(_uu),_Sx=jsFind(_Sw);if(!_Sx[0]){return new F(function(){return _y5(_Sw);});}else{var _Sy=E(_uz),_Sz=_Sy(E(_Sx[1])),_SA=_Sy(_Sz),_SB=E(_Sf)(_SA,toJSStr(E(_Sg)));if(!_SB){return _9W;}else{var _SC=rMV(_Sl),_SD=E(_SC),_SE=B(_y8(_Sn,_SD[1],_SD[2],_SD[4],_SD[5],_SD[6],_SD[7],_SD[8],_)),_=wMV(_Sl,E(E(_SE)[2]));return _9W;}}},_SF=B(A(_ks,[_3b,_w,_r,_ux,_BA,_So,_])),_SG=function(_SH,_){var _SI=rMV(_Sl),_SJ=_SI,_SK=new T(function(){var _SL=E(_SJ),_SM=_SL[1],_SN=new T(function(){return B(_B7(E(_SH)[1],_Bz,_SM));});return [0,_SN,_SL[2],_SL[3],_SL[4],_SL[5],_SL[6],_SL[7],_SL[8]];}),_=wMV(_Sl,_SK);return _9W;},_SO=B(A(_ks,[_3b,_w,_r,_ux,_BB,_SG,_])),_SP=rMV(_Sl),_SQ=E(_SP),_SR=B(_y8(_Sn,_SQ[1],_SQ[2],_SQ[4],_SQ[5],_SQ[6],_SQ[7],_SQ[8],_)),_=wMV(_Sl,E(E(_SR)[2])),_SS="battle",_ST=jsFind(_SS);if(!_ST[0]){return new F(function(){return _y5(_SS);});}else{return new F(function(){return _l0(_ST[1],_Sl,_);});}},_SU=function(_){return new F(function(){return _Sh(_);});};
var hasteMain = function() {B(A(_SU, [0]));};window.onload = hasteMain;