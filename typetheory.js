var USE_MATHJAX=true
var DARK_MODE=true
var USE_FASTNAT=true 
var DEBUG_MODE=true
var SHOW_LONG_NATS=true
//Not working:: R.times(R.plus(3,7),R.plus(4,5))
//Type theory rules
// x:A, f:A->B              f (x) : B
// x:A, y:B                 (x,y) : A x B
// x:A  ∀(_y:A) f (_y)      f (x) : B (x)
// x:A, y: B (x)            (x,y) : ∃(_y:A) B (_y)
//https://www.w3schools.com/js/tryit.asp?filename=tryjs_editor
// x⇒f(x): (_z:A)⇒B  == A->B (?)

/*
//---function and forall have different types
def h:= forall (x:Nat) y, x=y   :Prop
def g:= fun (x:Nat) y => x=y    :(x,y:Nat)->Prop
*/

var inputID=0;
function createInput(text ,element){
    inputID++;
    var rows = text.split("\n").length
    var s=
    `<textarea rows=${rows} id=example${inputID} class="input" spellcheck="false">${text}</textarea>
    <button onclick="go(${inputID},true)">PRINT</button>
    <button onclick="fullsimplify(${inputID})">SIMP</button>
    <button onclick="simplify(${inputID})">SIMP ONCE</button>
    <button onclick="tofloat(${inputID})">FLOAT</button>
    <button onclick="showEqGraph(${inputID})">EQ GRAPH</button>
    <button onclick="doDefEval(${inputID})">DEFEVAL</button>
    <button onclick="doExpandNats(${inputID})">EXPAND NATS</button>
    <div id="output${inputID}" class="outputbox"></div>
    `
    if(element) element.innerHTML+=s;
        else
    document.write(s)
    //go(inputID,true)
    setTimeout(()=>updateAll(),500 )
}

function updateAll(){
    for(var i=1;i<=inputID;i++){
        go(i,true)
    }
}

function dir(obj){
    var keys = [];
    var s=""
    for(var key in obj){
      output.innerHTML+=key+" ("+(typeof obj[key])+")<br>"
    }
 }

 //see also showVariables
 function showAll(n=1000000){
    var i=0
    var obj=dict
    for(var key in obj){
        if(obj[key]!=null && obj[key].kind!=undefined){
            //output.innerHTML+=key+"<br>";
            try{
                print(key+"="+fill(obj[key].toString())+":"+fill(obj[key].type.toString()))
            }catch{
                print("Error printing "+key)
            }
            i++;
        } else{
            //output.innerHTML+=key+" kind=undefined<br>"
        }
        if(i>n) break;
    }
    MathJax.typeset()
 }

/******************

Rules are Propositions:

mulRuleProposition = FORALL( Type, F=>FORALL( F, a=> FORALL( F, b=> equals(a+b,b+a) ))) 
mulRuleProof : mulRuleProposition
We can define a made up rule as [NO_PROOF] : mulRuleProposition

*****************/

var dict={}

function subscript(s){
    if(USE_MATHJAX) return "_{"+s+"}"
    return "<sub>"+s+"</sub>"
}

var output=document.getElementById("output")
var result=null;
var results=[0];
var currentCell=0;

function fill(f){
    while(typeof f=='function'){
        f= f("■")
    }
    return f
}

function noblank(f){
    return f=="■"?"":f;
}

//not good!
function showVariables(){
    var v=Object.keys( window )
    for(var i=numberWinVariables;i<v.length;i++){
        var result = eval(v[i])
        if(result!=null && typeof result!='function'){
            var type=""
            var t = result.type
            if(t!=null) type+=" : "+t
            print(normal(v[i]) +"   =   "+fill(result.toString()) + type)
        }
    }
    if(USE_MATHJAX) MathJax.typeset()
}

var currentID = 0;

function go(ID,clear){
    tempNum=0
    currentID= ID
    output=document.getElementById("output"+ID)
    if(clear) output.innerHTML="";
    var text=document.getElementById("example"+ID).value
    text=text.replace("∀","FORALL")
    
    lines = text.split(";")
    for(var i=0;i<lines.length;i++){
        text=lines[i];
        var lastresult=result;

        if(DEBUG_MODE)  result = eval(text)
        else{
            try {
                result = eval(text)
            } catch (e) {
                //if (e instanceof SyntaxError) {
                print(normal(e.message))
                MathJax.typeset()
                return
            }       
        }

        result = evalObject(result)
        if(result!=null){
            var type=result.type
            if(type==undefined)
                print(normal(result.toString()))
            else{
                print(fill(result.toString()) + " : " +fill(result.type.toString()))
            }
        }else result=lastresult;
        
    }

    results[ID] = result;

    if(window.MathJax!=undefined)
    MathJax.typesetPromise([output]).then(() => {
        //console.log("Typesetting complete.");
    }).catch((err) => console.error(err.message));

    //MathJax.typeset()
}

function evalObject(result){
    if(result!=null){
        if(typeof result==='number') {
            result = guessNumberType(result)   
        }
        if(typeof result==='boolean'){
            result = result?True:False;
        }
        if(typeof result==='string') {
            result = NewStringObj(result)  
        }
        if(result instanceof Array){    
            result = toList(result)
        }
    }
    return result
}


function guessNumberType(result){
    if(result!=Math.floor(result)) return toRat(result)
    else if(result<0 ) return toInt(result ) 
    else return N(result)    
}
function toList(list ,type=null){
    if(type==null){
        if(list.length==0) type=Nat;
        else{
            var L0=list[0];
            if(typeof L0 =='number') L0 = guessNumberType(L0)  
            if(typeof L0 =='string') L0 = NewStringObj(L0) 
            if(typeof L0 =='boolean') L0 = L0?True:False;
            if(L0 instanceof Array) L0 = toList(L0)
            type=L0.type
        }
    }
    var L=LEnd(type)
    for(var i=0;i<list.length;i++){
        L=LNext(type, list[i],L)
    }
    return L
}

function toVect(list,type){
    var L=toList(list,type)
    return Vector.fromList(L.type.second, list.length, L)
}
/*
function toFastList(list, type=null){
    if(type==null){
        var L0=list[0];
        if(typeof L0 =='number') L0 = guessNumberType(L0)  
        type=L0.type
    }
    var L=LEnd(type)
    for(var i=0;i<list.length;i++){
        L=LNext(type, list[i],L)
    }
    return L
}*/

function LIST(...args){
    return toList(args)
}

function VECT(...args){
    var list = toList(args);
    return Vector.fromList(list.type.second, args.length, list)
}

/*
function toList(result){

    var L=LEnd
    
    for(var i=0;i<result.length;i++){
        var K=eval(result[i])
        APPLY(K.)
    }
}*/

function ToggleMathjax(){
    USE_MATHJAX=!USE_MATHJAX
    if(USE_MATHJAX) MathJax.typset()
}

function tofloat(inputID){  
    var outputName=`output${inputID}`
    output=document.getElementById(outputName)
    result = results[inputID].float()
    output.innerHTML+=result
    //results[inputID] = result //??
}

function showEqGraph(inputID){  
    currentID=inputID
    var outputName=`output${inputID}`
    output=document.getElementById(outputName)
    eqGraph(results[inputID])
}

function simplify(inputID){  
    var outputName = `output${inputID}`
    output=document.getElementById(outputName)
    result = SIMP(results[inputID])
    results[inputID]=result;
    print(fill(result.toString()) + " : " +result.type)
    MathJax.typeset()
}
function jax(x){
    if(USE_MATHJAX) return "\\("+x+"\\)"
    else return x
}

function fullsimplify(inputID){  
    var outputName = `output${inputID}`
    output=document.getElementById(outputName)
    result = SIMP(results[inputID],M=1,fullsimp=true)
    results[inputID]=result;
    print(fill(result.toString())+" : " +result.type)
    MathJax.typeset()
}

function doDefEval(inputID){
    var outputName = `output${inputID}`
    output=document.getElementById(outputName)
    //result=REBUILD(result)
    result = DEFEVAL(results[inputID])
    //result=REBUILD(result)
    results[inputID]=result
    print(fill(result.toString())+" : " +result.type)
    MathJax.typeset()
}

function doExpandNats(inputID){
    var outputName = `output${inputID}`
    output=document.getElementById(outputName)
    result = ExpandNats(results[inputID])
    results[inputID]=result
    print(fill(result.toString())+" : " +result.type)
    MathJax.typeset()
}

function cls(){
    output.innerHTML="";
}

function sorry(t){
    if(t.type.symbol!=Prop.symbol){
        print(normal("Sorry type should be a proposition. Got: ")+t.type)
    }
   return new C(red("⚠"),t)
}
var unproved=sorry

function REWRITE(x,t,lemma,n=1){
    this.source=x
    this.kind="RW"
    this.type=t
    this.lemma=lemma
    this.n=n
}
REWRITE.prototype.toString=function(){
    return "RW("+this.source+"◀"+this.lemma+"])"
}

class C {
    constructor(a, t) {
        const inst = function (...args) {
            return inst.apply(...args)
        }

        //const instance=this
        inst.symbol = a
        inst.type = t
        inst.kind = "atom"
        inst.postfix = false
        inst.bold = false
        inst.notation = a

        Object.setPrototypeOf(inst, C.prototype)

        return inst
    }
    apply(...args) {
        var N = this
        for (var i = 0; i < args.length; i++) {
            N = APPLY(N, args[i])
            //N = apply(N,args[args.length-1 -i])
        }
        return N
    }
    to(x) {
        return new F(this, x)
    }
    float() {
        if (FastNat && this.symbol == FastNat.symbol) return Number(this.value)
        if (this.liveVal) return this.fastValue()

        else
            return this.fastValue
    }
    toString() {
        if (this.symbol == "?") {
            if (wilds[this.value]) return wilds[this.value].toString()
        }
        if (this.notation != null) return this.notation
        if (this.bold) return red(bold(this.symbol))
        return this.symbol
    }
    by(f) {
        return f(this)
    }
    inputForm(){      
        if(this.symbol=="FastNat") return this.value
        return this.symbol
    }
}



function Var(x,y, def=false){
    if(!y){
        console.log("Type not defined for "+x+". Using Type")
        y=Type
    }
    if(y.type.symbol==Prop.symbol && !def){
      //  print(red(normal("⚠Warning⚠ Creating a proof object "+x+" without proof!")))
    }
    var result = new C(x,y)
    dict[x] = result
    if(!window[x])
        window[x] = result; //<<----experimental
    else{
       // console.log(x+" is already a variable!");
    }
    return result
}

var AXIOM=Var

function NewType(x){
    return Var(x,Type)
}
function NewProp(x){
    return Var(x,Prop)
}

function defineVar(name, def, notation){
    tempNum=0
    var a = Var(name,def.type)
    a.notation = notation
    a.def = def
    if(def){
        if(!def.type.type.equals){
            print("Warning: "+def.type.type+" has no equals defined")
            a.proof = ErrorObject
        }else{
            a.proof = Var(name+".proof",def.type.type.equals(def.type, a , def) ,true)
        }
    }
    if(a.def.float)
    a.fastValue = a.def.float() //<-- default(?)
    return a
}
var ALIAS=defineVar

function defineFun1(name, def, notation){  //NOT COMPLETE
    var a = Var(name, def.type)
    a.notation = notation
    a.def = def
    a.prop = Var(name+".proof", equals(def.type, a , def) )
    return a
}

function ListSymbols(){
    var keys=Object.keys(dict)
    for(var i=0;i<keys.length;i++){
        print(dict[keys[i]]+" : "+ dict[keys[i]].type)
    }
    if(USE_MATHJAX) MathJax.typeset()
    return null;
}
var Type3= orange("\\mathscr{T3}")
var Type2= new C(orange("\\mathscr{T2}"),Type3)
var Type1=new C("Type1",Type2); Type1.notation = orange("\\mathscr{T1}");
var Type=new C("Type",Type1) ; Type.notation = orange("\\mathscr{T}");

var ErrorMessage =new C(red("ERROR"),Type)
var ErrorObject = new C("⚠",ErrorMessage); ErrorObject.notation=red("⚠");

var Prop= new C("Prop",Type) ;Prop.notation=pink("Prop");

var wilds={}

function Wild(t){
    var wild = new C("?",t)
    wild.value = getUniqueName()
    return wild
}
// A x B

function P(a,b){
    this.type = a.type+" × "+b.type
    this.kind = "pair"
    this.first = a
    this.second= b
}

P.prototype.toString = function(){ 
    //return "("+this.first+","+this.second+")";
    return "("+this.first+" ◁ "+this.second+")";
}
/*
function Exists(x, f){
    this.kind =  "exists"
    this.vari= x
    this.func = f
    this.first=x.type
    this.second= f(x)
    this.type = this.second.type
}

Exists.prototype.toString = function(){ 
    if(USE_MATHJAX) return "\\bigvee\\limits_{"+this.vari+":"+this.first+"}"+this.second;
    //return "∃("+this.vari+":"+this.vari.type+"),"+this.second;
    //return "("+this.vari+":"+this.vari.type+" ◁ "+this.second+")";
}
*/
//dependent pair????NO INTRO?




class Applied {
    constructor(a, b, t) {
        const inst = function (...args) {
            return inst.apply(...args)
        }

        inst.first = a
        inst.second = b
        inst.type = t
        inst.kind = "applied"
        inst.posfix = false
        inst.notation = null
        inst.symbol = "∘"

        Object.setPrototypeOf(inst, Applied.prototype)
        return inst
    }
    to(x) {
        return new F(this, x)
    }
    apply(...args) {
        var N = this
        for (var i = 0; i < args.length; i++) {
            N = APPLY(N, args[i])
        }
        return N
    }
    by(f) {
        return f(this)
    }
    float() {
        var firstValue = this.first.float()
        var secondValue = typeof this.second.float == 'function' ? this.second.float() : null
        // if(!firstValue) console.log("No getFast on" + fill(this.first.toString())+" "+this.first.kind)
        // if(!secondValue) console.log("No getFast on" + fill(this.second.toString())+" "+this.second.kind)
        if (typeof firstValue != 'function') {
            //console.log(fill(this.first.toString())+" not a function  ")
            return null
        }
        //console.log(this.kind+","+this.second.kind+" "+this.second.symbol+" ("+secondValue+")")
        return firstValue(secondValue,this.second) //second argument useful for setting values, for example
    }
    fastValue() {
        console.log("HELLO")
    }
    toString() {
        if (this.notation) return this.notation
        var firstString = this.first.toString()
        var secondString = this.second.toString()
        if (typeof firstString == 'function') return firstString(secondString, this.second)


        if (this.first.postfix)
            return (this.second.kind == "applied" ? "(" + secondString + ")" : secondString + " ") + this.first
        else {
            if (this.first.kind != "fun")
                return firstString + "(" + fill(secondString) + ")"

            else
                return "(" + firstString + ")(" + fill(secondString) + ")"
            //return firstString+ (this.second.kind=="applied"?"("+ secondString+")" :" "+ secondString  )
        }
    }
    inputForm(){
        return this.first.inputForm() + "(" + this.second.inputForm() + ")"
    }
}


class AppliedList{
    constructor(){
        this.first=null
        this.second=[]
        this.symbol="ApplyTo"
        this.color="lightgreen";
        this.kind="AL";
        this.type=Type;
    }
    toString(){
        var result = this.first.toString() + "(";
        for(var i=0;i<this.second.length;i++){
           result+=fill( this.second[i].toString());
           if(i<this.second.length-1) result+=",";
        }
        return result+")";
    }
    getTypeInputForm(){
        var result="";
        for(var i=0;i<this.second.length;i++){
            //if(i>0) result+=".to("
            result+=this.second[i].type.inputForm()
            //if(i>0) result+=")";//"→"
            if(i<this.second.length-1) result+="→"
        }
        return result + "→?"
    }
}

function toAppliedList( B ){
    var A = new AppliedList();
    while(B.kind == "applied"){
        A.second.unshift(B.second)
        B = B.first;
    }
    A.first = B;
    return A;
}




function showRealSeries(f){
    var s="\\{";
    for(var i=0;i<3;i++){
        s+=f.apply(i)+","
    }
    s+="...\\}"
    return s
}


//-------------------------------------------------------------------
//  A->B



class F {
    constructor(a, b) {
        this.kind = "imply"
        this.first = a
        this.second = b
        //convenience:
        this.symbol = "→";
        this.func = "!!!" //_ => this.second
        this.type = b.type //(Use second type)
    }
    appliedTo(X) {
        return this.second
    }
    toString() {
        return Fbracket(this.first) + "→" + this.second
    }
    to(x) {
        return new F(this, x)
    }
    inputForm(){
        return this.first.inputForm()+".to("+this.second.inputForm()+")"
    }
}
function Fbracket(x){
    if(x.kind=="imply") return "("+x+")"
    return x
}


class ForAll {
    constructor(x, f) {
        this.kind = "forall"
        this.vari = x
        this.func = "!!!!!!" //f
        this.first = x.type
        this.second = f ? f(x) : null
        this.symbol = "∀"
        this.color="orange"
        this.type = this.second ? this.second.type : null //inherits type?//f(x).type
        if(this.type && this.type.symbol!=Type.symbol && this.type.symbol!=Prop.symbol) this.type = this.second.type.type; //hackish
        
        //console.log("ForAll Const" + this.first)
    }
    to(x) {
        return new F(this, x)
    }
    appliedTo(X) {
        //var type= this.second.type
        //console.log("Forall replace "+this.vari+" "+X);
        var result = REPLACE(this.second, this.vari, X)
        //console.log(result.toString())
        //result.type = REPLACE(this.second.type,this.vari,X)
        return result
    }
    toString() {
        var tempVari = new C(getNewVariName(), this.first)
        var second = this.appliedTo(tempVari) //this.func(tempVari)

        //return "\\bigwedge\\limits_{"+this.vari+":"+ this.first+"}"+fill(this.second.toString());
        if (USE_MATHJAX) return "\\bigwedge\\limits_{" + tempVari + "\\in " + this.first + "}" + fill(second.toString());
        return red(bold("∀")) + "(" + tempVari + ":" + this.first + ")," + fill(second.toString())
    }
    inputForm(){
        var tempVari = new C(getNewVariName(), this.first)
        var second = this.appliedTo(tempVari) 
        return "FORALL("+this.type.inputForm()+","+tempVari.inputForm()+"=>"+second.inputForm()+")"
    }
}


function FORALL(t,f){
    //console.log("FORALL "+t);
    return new ForAll( new C(getUniqueName(t),t) , f )
}

function marks(n){
    var s="";
    for(var i=0;i<n;i++) s+="'"
    return s;
}

function getSimpleVariName(){
    var result = String.fromCharCode(97 + tempNum%26)+marks(Math.floor(tempNum/26));
    tempNum++;
    return result;
}


function getNewVariName(t){
    var result="??"
    if(t && t.symbol==Type.symbol) result = color(cal(String.fromCharCode(65 + tempNum%26)+marks(Math.floor(tempNum/26))),"purple")           // +subscript(t)
    else result = color(String.fromCharCode(97 + tempNum%26)+marks(Math.floor(tempNum/26))/*+"'"*/, "green")           //  +subscript(t)
    //console.log(tempNum)
    tempNum++;
    return result
}

var uniqueID=BigInt(0)
function getUniqueName(){
    return "@["+(uniqueID++)+"]"
}


var DOIT=true;

//better if it's Fun(type, f)
class Fun {
    constructor(x, f) {

        const inst = function (...args) {
            return inst.apply(...args)
        }

        Object.setPrototypeOf(inst, Fun.prototype)

        inst.kind = "fun"
        //inst.vari = new C(getUniqueName(t),t) //Should we have this at all???
        inst.vari = x //new C(getUniqueName(t),t)
        inst.func = "!!!" //f
        inst.first = x.type
        inst.second = f ? f(x) : null
        inst.symbol = "⇒"
        inst.color = "cyan";

        //check if it contains the variable then it is dependent type
        if( ContainsVar(inst.second.type, x ) )
            inst.type = FORALL(inst.first, x => f(x).type) //new ForAll(inst.vari, x => f(x).type) //might be slow?
        else {
            inst.type = new F(inst.first, inst.second.type)
        }

        return inst
    }
    toString() {
        //return "\\lambda_{("+this.vari+":"+this.first +")}." + this.second
        var tempVari = new C(getNewVariName(), this.first)
        var newsecond = REPLACE(this.second, this.vari, tempVari)

        return "(" + tempVari + ":" + this.first + ")⇒" + fill(newsecond.toString())
        //return "("+this.vari+":"+this.first +")⇒"+this.second.toString;
    }
    apply(...args) {
        var N = this
        for (var i = 0; i < args.length; i++) {
            N = APPLY(N, args[i])
            //N = apply(N,args[args.length-1 -i])
        }
        return N
    }
    appliedTo(X) {
        var r = REPLACE(this.second, this.vari, X)
       //if(this.type.appliedTo) r.type = this.type;
        if (this.type.appliedTo && DOIT)  r.type = this.type.appliedTo(X)
        //    r.type = REPLACE(this.type, this.vari,X)   //this.type.appliedTo(X)
        return r
    }
    float(){      
        return x=>{
            /*return 0;
            var vari = new Var("X",this.first); 
            vari.fastValue = x;
            return this(vari) //<--probably slows things down*/

            //****WARNING THIS ASSUMES vari has same pointer for all it's appearances! */
            var temp=this.vari.fastValue
            this.vari.fastValue = x;
            var result = this.second.float?this.second.float(): null;
            this.vari.fastvalue = temp;
            return result;
        }
    }
    inputForm(){
        var tempVari = new C(getNewVariName(), this.first)        
        var newsecond = REPLACE(this.second, this.vari, tempVari)
        return "FUN("+this.first.inputForm()+","+tempVari.inputForm()+"=>"+newsecond.inputForm()+")"
    }
}


function ContainsVar(A,X){
    if(A.symbol==X.symbol) return true;   
    return (A.first && ContainsVar(A.first,X)) || (A.second && ContainsVar(A.second,X))
}



//complexGraph( FUN(CR,z=>iter(CR, FUN(CR, x=>CR.plus(CR.times(x,x),z) ) , z , 10) ))

function FUN(t,f){
   // console.log(t.symbol)
    return new Fun( new C(getUniqueName(t),t) , f )
    //return new Fun( t , f )
}


function infer(a,b){
    return new F(a, b)
}

function typeOf(a){
    return a.type
}
function print(a){
    tempNum=0
    if(output){
        if(USE_MATHJAX )output.innerHTML+=jax(a)+"<br>"
        else output.innerHTML+=a+"<br>"
    }else{
        console.log(a)
    }
   // if(MathJax!=null)
   // MathJax.typeset()
}

function tryToConvertNumber(A,b){ //convert javascript-numerical b to type A
    if(A.symbol==Nat.symbol ) b = N(b)
    else if(A.symbol==Int.symbol) b = toInt(b)
    else if(A.symbol==Rational.symbol) b=toRat(b)
    else if(A.symbol==Float64.symbol) b=toFloat64(b)
    else if(A.symbol==Float32.symbol) b=toFloat32(b)
    else if(A.symbol==Float16.symbol) b=toFloat16(b)
    else if(A.symbol==Real.symbol) b=toReal(b)
    else if( equiv(A, R2R) ) b=toConstFunc(b)
    else if(A.kind=="applied"){
        if(A.first.symbol == Zmod.symbol) b= Zmod.fromNat( A.second ,b)       
        if(A.first.symbol == Complex.symbol) b = ComplexMk(A.second)(  tryToConvertNumber(A.second,b) ,0)        
        if(A.first.symbol == Quaternion.symbol) b = QuaternionMk(A.second)(  tryToConvertNumber(A.second,b)  ,0,0,0)       
        if(A.first.symbol == Octonion.symbol) b = OctonionMk(A.second)(  tryToConvertNumber(A.second,b)  ,0,0,0,0,0,0,0)       
    }
    else if(A.symbol=="?"){  //doesn't really work at moment for dependent types
        console.log("Guessing number")
        b=guessNumberType(b)
        wilds[A.value] = b.type
    }
    else{
        print(red(normal("⚠ Can't convert number to  : "))+fill(A.toString()));
        if(USE_MATHJAX) MathJax.typeset();
        b = ErrorObject
    }    
    return b
}


function APPLY(a,b){  /// a(b)// where a:A->B or a:Forall(x:A=>B(x))
    //print(a.type.first+"=?="+b.type+"  "+a.kind)
    
    if(a.ignore>0 && b.symbol!="?"){
        for(var i=0;i<a.ignore;i++){
            console.log("YES" +i)
            a = APPLY(a,Wild(Type)) //must get the type
        }
    }
    //plus.ignore=1
    //plus(plus(1,2),4.3) //not working correctly

    var expectedType = a.type.first
    if(a.type.first.symbol=="?"){
        console.log("Wild card found")
        if( wilds[a.type.first.value]){
            expectedType = wilds[a.type.first.value]
            console.log("Type found "+expectedType)
        }else{
            console.log("No type found")
            if(typeof b != "number"){
                wilds[a.type.first.value] = b.type
                expectedType = b.type
            }
        }
    }


   /* if(a.hasWildCard){ //clear wild cards
        wilds[this.hasWildCard] = null
    }*/


    if(!a.type.first){
         print(red(normal("This is not a function: "))+a); 
        if(USE_MATHJAX) MathJax.typeset();
        //return null;
        return ErrorObject
    }

    //turn numbers into nats?
    if(typeof b ==='number'){
        b=tryToConvertNumber(expectedType,b) 
        expectedType=b.type
    }
    if(typeof b=='boolean'){
        b = b?True:False;
        expectedType = Prop;
    }
    if(typeof b ==='string'){
        b = NewStringObj(b)
        expectedType = mystring
    }
    if(b instanceof BigInt){
        var result = NewFastNat(b)
        result.notation = "["+b+"]"+subscript("ℕ")
        b=result
    }

    //fast check first?
    if ( !equiv(expectedType,b.type)){
        //if(a.type.first != b.type) {  //   :N->M
        //checking definitional equality
        if(! DEFEQUIV( expectedType,b.type) ){
            var warning=red(normal("⚠"))+fill(a.toString())+red(normal(" expected ■ : "))+fill(expectedType.toString()) +red(normal("  Got "))+fill(b.toString()) + " : "+b.type
            console.log(warning)
            print(warning);
            print(blue(normal("(Failed definitional equality check)")))
            if(USE_MATHJAX) MathJax.typeset();
            b = ErrorObject
            //return null;
        }else{
            print(blue(normal("(Using definitional equality)")))
        }
    }
    
    if(a.type.appliedTo){ 
        if(a.kind=="fun") return a.appliedTo(b); // causing it not to be a function???
        if(a.type.kind=="fun") {
            print("Probably an error here!!! type kind should not be FUN for"+fill(a.toString()))
            return a.appliedTo(b)
        }
        var result = new Applied(a,b, a.type.appliedTo(b) )
    /* if(b.symbol=="?"){
            result.hasWildCard = b.value
        }*/
        return result       
    }
    print(normal("Error: Not a function type: ")+a.type); 
    if(USE_MATHJAX) MathJax.typeset();
    return null;
}

var tempNum=0
function clearArray(a){
    for(var i=0;i<a.length;i++){
        a[i]=null;
    }
}


//number to nat
function N(n){
    n=Math.floor(n)
    n=n>=0?n:0 //ignore negative numbers
    //console.log("Warning negative number ")
    if(USE_FASTNAT){
        //if(n==0) return zero;
        //if(n==1) return one;
        //else 
        return NewFastNat(BigInt(n))
    }
    return Unary(n)
}

function Unary(n){
    var result=zero
    for(var i=0;i<n;i++){
        result = succ.apply(result)
    }
    return result
}

function toInt(n){
    if(n>=0) return IntMk.apply(n,0)
    else return IntMk.apply(0,-n)
}

Number.prototype.countDecimals = function () {
    if(Math.floor(this.valueOf()) === this.valueOf()) return 0;
    return this.toString().split(".")[1].length || 0; 
}

function gcd(a, b) {   // 6   5
    while(b){
        var temp = b  
        b = a%b       
        a = temp     
    }
    return a;
}

function decimalToFraction(decimal, tolerance = 1.0e-15) {
    let sign = decimal < 0 ? -1 : 1;
    decimal = Math.abs(decimal);

    let h1 = 1, h2 = 0;
    let k1 = 0, k2 = 1;
    let b = decimal;
    do {
        let a = Math.floor(b);
        let aux = h1;
        h1 = a * h1 + h2;
        h2 = aux;

        aux = k1;
        k1 = a * k1 + k2;
        k2 = aux;

        b = 1 / (b - a);
    } while (Math.abs(decimal - h1 / k1) > decimal * tolerance);

    return { numerator: sign * h1, denominator: k1 };
}

function toRat(n){
    var sign=1;
    if(n<0) { n=-n; sign=-1;}
    if(Math.floor(n)==n) return RationalMk.apply(sign*n,1)
    else {
        //var den = Math.pow(10,n.countDecimals())
        //var num = Math.floor(n*den+0.5)
        
        var r = decimalToFraction(n)
        var den=r.denominator;
        var num=r.numerator;
        console.log(num+"/"+den)
        var GCD = (num>den)? gcd(num,den) : gcd(den,num)
        return RationalMk.apply( sign*(num/GCD),den/GCD)
    }
}

function toFloat64(n){
    var result = new C("{"+n+"}"+subscript("f64"), Float64)
    result.value = n;
    return result;
}
function toFloat32(n){
    n = new Float32Array([n])[0];
    var result = new C("{"+n+"}"+subscript("f32"), Float32)//n.toPrecision(8)
    result.value = n
    result.fastValue = n;
    return result;
}
function toFloat16(n){
    var result = new C("{"+n+"}"+subscript("f16"), Float16) //n.toPrecision(4)
    result.value = n
    return result;
}

function toReal(n){
    var num = toRat(n)
    return Real.fromRat( num )
    //RealMk.apply(  FUN(Nat, x=> num  )    )
}
function toConstFunc(n){
    return R2R.fromReal(toReal(n))
}

function toComplex(F,n){
     return ComplexMk.apply(F,n,0)
}

function checkEquiv(a,b,varis=[]){
    RD.assigned=[]
    for(var i=0;i<varis.length;i++)
    RD.assigned.push(null)
    return equiv(a,b,varis)
}

//definitional equality
function defEqual(a,b){
    //a= SIMP(a,1,true)
   // b= SIMP(b,1,true)
   // return equiv(a,b)
   return false
}


function equiv(a,b, varis=[], RD=new ReplaceData()){ 

    //Check WildCards in b that match with a
    for(var i=0;i<varis.length;i++){
        if(b.symbol==varis[i].symbol){
            if( equiv(a.type , varis[i].type, varis, RD) //<---could be a problem with dependent types!
            && ( RD.assigned[i]==null    || equiv(a,RD.assigned[i],[]))  ){ //<--- WARNING! a cannot depend on any function variables!!!
                //print(i + " FOUND " +b.symbol +"-->"+a)
                RD.assigned[i] = a
                return true
            }
            else return false
        }
    }

    //Comparing fastnats S(S(S(2))) to S(S(3)) for example
    if(FastNat!=undefined && succ!=undefined){
        if(b.symbol==FastNat.symbol){ 
            if(a.symbol == FastNat.symbol) return b.value==a.value
            if(a.symbol == zero.symbol) return b.value==0
            if(a.kind=="applied" && a.first.symbol==succ.symbol){ 
                return b.value!=0 && equiv(a.second, NewFastNat(b.value-BigInt(1))  , varis,RD )
            }
            return false
        }
        if(a.symbol==FastNat.symbol){  
            if(b.symbol == FastNat.symbol) return a.value==b.value
            if(b.symbol == zero.symbol) return a.value==0        
            if(b.kind=="applied" && b.first.symbol==succ.symbol){ 
                return a.value!=0 && equiv(NewFastNat(a.value-BigInt(1)) ,b.second, varis,RD )        
            }
            return false
        }
    }


    if(a.value!=b.value) return false //fastnat
    
    if(a.kind!=b.kind) {
        return false
    }
    if(a.kind=="atom" ) return a.symbol==b.symbol 
    if(a.kind=="applied"|| a.kind=="imply" || a.kind=="pair"){  //A(B),  A->B  (A,B)
        return equiv(a.first,b.first, varis,RD) && equiv(a.second,b.second, varis,RD) 
    }
    if(a.kind=="fun" || a.kind=="forall" || a.kind=="exists"){ //x->f(x), Ax,f(x), Ex, f(x)
        var X = new C(getUniqueName(), a.first)
        return equiv(a.first , b.first) && equiv( a.appliedTo(X) ,b.appliedTo(X) , varis, RD)
    }
    console.log("***UNKNOWN KIND "+a.kind+ " of "+a+"****")
    print("***UNKNOWN KIND "+a.kind+ "****")
    return false;
}

function EQUIV(a,b){
    if(equiv(a,b)) return True;
    else return False;
}

//MATCH( S(x), S(5), [x])
//better syntax = MATCH(Nat, S(5), x=>S(x) )  == IFMATCH( S(5), x=>S(x), x=>x, [Nat])
function MATCH( a,b, varis ){
    var RD=new ReplaceData()
    if(equiv(b,a,varis,RD))
    return RD.assigned
else return false
}
//IFMATCH(x=>S(x), x=>Nat.times(x,x), 0 , [Nat]) //we should be ablt to deduce types
//IFMATCH(x=>y=>Nat.plus(x,y), x=>y=>Nat.plus(x,y), 0 , [Nat,Nat] )
//F = FUN(Nat, z=>  IFMATCH( z, 0, 1, IFMATCH( z, x=>S(x),  S(x)*F(x), 0, [Nat]  )  , [Nat]))
//GETTYPE(x=>S(x))

//IFMATCH( Nat.plus(13,15), x=>y=>Nat.plus(x,y), x=>y=>[x,y], [Nat,Nat] )
function IFMATCH(a,b,c,types){
    var varis=[]
    var i=0
    while( b instanceof Function ){
        var x = new C(getUniqueName(),types[i++])
        varis.push(x)
        b=b(x)
    }
    var RD=new ReplaceData()
    equiv(a,b,varis,RD)
    for(var j=0;j<types.length;j++){
        c=c(RD.assigned[j])
    }
    return c
}


function contains(big, small){ 
    if(equiv(big,small)) return true;
    if(big.kind=="applied"|| big.kind=="imply" || big.kind=="pair"){
        return contains(big.first,small) || contains(big.second,small)
    }
    return false;
}

function cloneInstantiated(obj, forceClone=false) {
    if(!forceClone && obj.kind=="atom") return obj; //no need to clone atoms (Can cause problems if use FORALL wrongly)
    const newobj = Object.create(Object.getPrototypeOf(obj));
    Object.assign(newobj, obj);
    return newobj;
}


//---------REPLACE DOESN'T CHECK TYPES!!!! e.g. F->(x:F)->(y:F)-> (x+y:F=y+x:F    ) DOES IT NEED TO?------------------//
var replacementsFound=0

function REPLACE(big, small, newterm ,varis=[], RD=new ReplaceData()){
    var temp = RD.assigned.slice()
    if(equiv(big,small, varis,RD)  ) {
        replacementsFound ++ //not quite true! 
        if (RD.which=="All" || RD.which.indexOf(replacementsFound)>=0) {
            return newterm; //<----Let's not clone it. Will this be problem???
        } 
        
        //cloneInstantiated(newterm) //<--- do replacement here???
    }
    RD.assigned=temp
    //Shouldn't match things in functions(?)
    if(big.kind=="applied"|| big.kind=="imply" || big.kind=="pair" || big.kind=="rule"){ //forall needed?
        var newbig = cloneInstantiated(big)
        newbig.first = REPLACE(big.first, small , newterm,varis,RD);
        newbig.second =  REPLACE(newbig.second, small, newterm,varis,RD);
        return newbig;
    }
    if(big.kind=="forall" || big.kind=="fun"){
        //var newtype =big.first;// REPLACE(big.first, small, newterm,varis,RD);
       //***********DUBIOUS KEEPING THE VARI NAME THE SAME BUT CHANGING IT'S TYPE*****  
        var vari= cloneInstantiated(big.vari, true);//new C(getUniqueName(), newtype)      
        var S = REPLACE(big.appliedTo(vari), small, newterm,varis,RD); //appliedTo overrides vari type!!!
        vari.type = REPLACE(big.vari.type, small, newterm,varis,RD)
        //if(big.type.appliedTo)
        //    S.type = REPLACE(big.type, small, newterm,varis,RD) //infinite loop
        //S.type=Nat       
        var newbig = big.kind=="fun" ?
         new Fun(vari, x=>REPLACE(S, vari, x)) :   new ForAll(vari, x=>REPLACE(S, vari, x))     
        
         return newbig;
    }
    if(big.kind!="atom")
        print(normal("kind not found in replace "+big.kind +" ")+fill(big.toString()))
    return cloneInstantiated(big)
}


function findMatch(big, small, newterm ,varis=[]){  //, RD.assigned=[]
    //var temp = RD.assigned.slice() //<-----------do we need this???
    if(equiv(big,small)){//, varis,RD)) {
        return true
    }//else RD.assigned=temp //<-----------do we need this???
    if(big.kind=="applied"|| big.kind=="imply" || big.kind=="pair" || big.kind=="rule"){ 
        return  findMatch(big.first, small)// , newterm,varis,RD)
            ||  findMatch(big.second, small)//, newterm,varis,RD)
    }
    if(big.kind=="forall" || big.kind=="fun"){
        //var newbig = cloneInstantiated(big)
        var firstmatch = findMatch(big.first, small)//, newterm,varis,RD);
        //var vari=new C(getUniqueName(), newtype)
        return firstmatch || findMatch(big.second, small)//, newterm,varis,RD); 
    }
    if(big.kind!="atom")
    print("kind not found in replace "+big.kind +" "+fill(big.toString()))
    return false
}



/*
function replaceFunc(big, small){  //, RD.assigned=[]
    if(equiv(big,small)) {
        replacementsFound ++
        return x=>x;
    }
    if(big.kind=="applied"|| big.kind=="imply" || big.kind=="pair" || big.kind=="forall" || big.kind=="fun"){ //forall needed?
       
            var newbig = cloneInstantiated(big)
            var firstFunc= replaceFunc(big.first, small)
            var secondFunc= replaceFunc(newbig.second, small)
            return x=>{
                newbig.first = firstFunc(x);
                newbig.second = secondFunc(x);
                return newbig
            }
    }
    if(big.kind!="atom")
    print("kind not found in replace "+big.kind)
    return x=>cloneInstantiated(big)
}*/




//var RD.assigned=[]
var debug=false

class ReplaceData{
    constructor(){
        this.assigned=[]
        this.which = "All"
    }
}


function replaceUsing(big, rule){
    var varis=[]
    var RD = new ReplaceData()
    var root=rule
     while(root.kind=="fun"){
        varis.push(root.vari)
        root = root.second       
        //root = root.appliedTo(root.vari)
        RD.assigned.push(null)
    }
    //print(fill(root.toString()))
    //if(!findMatch(big,root.first)) return big
    //***We sent RD.assigned by ref */

    var result = REPLACE(big, root.first, root.second, varis,RD)    

    if(RD.assigned.length==0 || !RD.assigned.includes(null) ){
    
        //var resultType= REPLACE(big.type, root.first, root.second, varis,RD)

        for(var i=0;i<varis.length;i++){
            //console.log("replace "+fill(varis[i].toString())+" with "+fill(RD.assigned[i].toString()));
            result = REPLACE(result,varis[i] , RD.assigned[i] )
          //  resultType = REPLACE(resultType,varis[i] , RD.assigned[i] )
        }
        result=REBUILD(result)
        //result.type= resultType
    }//else result = big

    return result
}

function replaceUsingEquality(big, rule){
    
    var varis=[]
    var RD=new ReplaceData()
    RD.assigned=[]
   var root=rule
     while(root.kind=="forall"){
        varis.push(root.vari)
        root = root.second
        //root = root.appliedTo(root.vari) //<--- this is the slow bit!!
        RD.assigned.push(null)
    }

    if(root.kind!="applied" || root.first.first.first.symbol!=equals.symbol) { //equals F, x , y A(A(A(equals,F),x),y)
        print("ERROR not an equal")
    }
    var type=root.first.first.second
    var x=root.first.second
    var y=root.second

    //if(!ContainsVar(big,x)) return big;
    //quick check:
    //for(var i=0;i<varis.length;i++){
    //    if( ! ContainsVar(big,varis[i])) return big;
   // }

    
    //var b = cloneInstantiated(big)
    //if(!findMatch(big,x)) return big
    var result= REPLACE(big, x,y, varis, RD)

    //WARNING--breaks if there is unused FORALL(n=> in rule---
    
//****We don't just replace type of parent object... have to replace type of all child components too! ****/

    if(RD.assigned.length==0 || !RD.assigned.includes(null) ){      
      //  console.log("Replacement2 found:"+RD.assigned.length+" " +rule);  
        //var resultType= REPLACE(big.type, x,y, varis, RD)
        for(var i=0;i<varis.length;i++){
            //console.log("replace2 "+fill(varis[i].toString())+" with "+RD.assigned[i].kind+" "+fill(RD.assigned[i].toString()));
            result = REPLACE(result,varis[i] , RD.assigned[i] )
          //  resultType = REPLACE(resultType,varis[i] , RD.assigned[i] )
        }
        //result.type= resultType
        result=REBUILD(result)
    }//else result = b


    

    return result

}

function RW(big, rules, repeat=1){
    for(var r=0;r<repeat;r++)
    for(var i=0;i<rules.length;i++){
        if(rules[i])
        big = replaceUsing(big,rules[i])
    }
    return big
}

function RW2(big, rules, repeat=1){
    for(var r=0;r<repeat;r++)
    for(var i=0;i<rules.length;i++){
        if(rules[i])
        big = replaceUsingEquality(big,rules[i].type)
    }
    return big
}

function Rule(a,b){
    this.first=a
    this.second=b
    this.kind="rule"
    this.type = new C("Rule["+a.type+"]",Type)
}
Rule.prototype.toString = function(){
    return this.first+" "+bold(":=")+" "+this.second 
}

function Rule2(varis,a,b){
    this.varis = varis
    this.first=a
    this.second=b
    this.kind="rule"
    this.type = "<font color=purple>Rule</font>"
}
Rule2.prototype.toString = function(){
    return applyVaris(this.first,this.varis.slice())+" := "+applyVaris(this.second,this.varis.slice())
}
function applyVaris(a,varis){
    if( varis.length==0) return a;
    var X=varis.pop();
    //print(a)
    return applyVaris( a(X), varis  )
}

function apply2(f,a,b){
    return apply(apply(f,a),b)
}
function apply4(f,a,b,c,d){
    return apply2(apply2(f,a,b),c,d)
}

function QE(n){
    return bold("e")+subscript(n)
}

function cal(n){
    return "\\mathcal{"+n+"}"
}


function bold(s){
    if(USE_MATHJAX) return "\\textbf{"+s+"}"
    return "<b>"+s+"</b>"
}
function italic(s){
    if(USE_MATHJAX) return "\\textit{"+s+"}"
    return "<i>"+s+"</i>"
}
function normal(s){
    if(USE_MATHJAX) return "\\text{"+s+"}"
    return s
}
function red(s){
    return color(s,"red")
}
function green(s){
    return color(s,"green")
}
function blue(s){
    return color(s,"blue")
}
function orange(s){
    return color(s,"orange")
}
function pink(s){
    return color(s,"pink")
}
function color(s,col){
    if(USE_MATHJAX) //return s;//
    return "\\textcolor{"+col+"}{"+s+"}"
    return "<font color="+col+">"+s+"</font>"
}

//-----------------SIMPLIFICATION-------------------------
function ApplyUnappliedFunctions(big){
    if(big.kind=="applied" && big.first.kind=="fun"){
        return APPLY(big.first, big.second)
    }
    
    if(big.kind=="applied"|| big.kind=="imply" || big.kind=="pair" || big.kind=="rule"){ //forall needed?
        var newbig = cloneInstantiated(big)
        newbig.first = ApplyUnappliedFunctions(big.first);
        newbig.second = ApplyUnappliedFunctions(big.second)
        return newbig;
    }
    
    if(big.kind=="forall" || big.kind=="fun"){ //need checking:
        var newtype = ApplyUnappliedFunctions(big.first);
        var vari=new C(getUniqueName(),newtype)
        //var newbig = cloneInstantiated(big)
        var s = ApplyUnappliedFunctions(big.appliedTo(vari))
        //newbig.second =  ApplyFastNats(big.second)
        return big.kind=="forall"? FORALL(newtype,x=>REPLACE(s,vari,x)): FUN(newtype,x=>REPLACE(s,vari,x))
    }
    if(big.kind!="atom")
    print("kind not found in replace "+big.kind)
    return cloneInstantiated(big)
}


function REBUILD(big){    
    if(big.kind=="applied"){
        return APPLY(REBUILD(big.first),REBUILD(big.second))
    }
    if(big.kind=="fun" ){//???
        var newVari = new C(getUniqueName(),  REBUILD(big.first))
        //var newVari= cloneInstantiated(big.vari, true)
        //var S=REBUILD(big.second)
        var S=REBUILD(big.appliedTo(newVari )) //REBUILD(big.second)
        return new Fun(newVari, x=>REPLACE(S, newVari, x)) //<-- part of the problem is we are using REPLACE(!!!)
    }
    //if(big.kind!="atom")
    //print("kind not found in replace "+big.kind)
    //return big
    
    return cloneInstantiated(big)
}


//-----------------SIMPLIFICATION-------------------------
function ExpandNats(big){    
    if(typeof big === 'number') return Unary(big)

    if(big.kind=="applied"|| big.kind=="imply" || big.kind=="pair" || big.kind=="rule"){ //forall needed?
        var newbig = cloneInstantiated(big)
        newbig.first = ExpandNats(big.first);
        newbig.second = ExpandNats(big.second)
        return newbig;
    } 
    if(big.kind=="forall" || big.kind=="fun"){ //need checking:
        var newtype = ExpandNats(big.first);
        var vari=new C(getUniqueName(),newtype)
        //var newbig = cloneInstantiated(big)
        var s = ExpandNats(big.appliedTo(vari))
        return big.kind=="forall"? FORALL(newtype,x=>REPLACE(s,vari,x)): FUN(newtype,x=>REPLACE(s,vari,x))
    }
    if(big.kind!="atom")
    print("kind not found in replace "+big.kind)
    if(big.symbol == FastNat.symbol){
        //return S(S(S(S(0))))
        var n=big.value
        return Unary(n)
    }
    return cloneInstantiated(big)
}


function NewFastNat(val){
    var result = new Var(FastNat.symbol, Nat)
    result.value = val
    result.notation = fastNatNotation(val)
    result.fastValue= val;
    return result
}

function NewStringObj(val){
    var result = new Var("string"+getUniqueName(), mystring)
    result.value = val
    result.notation = normal("“"+val+"”")
    result.fastValue= val;
    return result
}

function NewFastList(type,val){
    var result = new Var("FastList", List(type))
    result.value = val

    var s="\\{";
    for(var i=0;i<Math.min(4,val.length);i++) s+=val[i]+","
    result.notation = s+"...\\}";//"\\{...\\}"
    result.fastValue = val;
    return result
}

function ApplyFastNats(big){
    //MATCH(A[A[A[ (plus/times/divide/sub),Nat],FastNat],FastNat])
    //if(equiv(big, F(Nat,X,Y),[F,X,Y]) && X.symbol==FastNat && Y.symbol==FastNat    )
    if(big.kind=="applied" && big.first && big.first.first && big.first.first.first && big.first.first.second.symbol == Nat.symbol){
        //print("FOUND" + big.first.first.first.symbol+" "+times.symbol)
        var symbol = big.first.first.first.symbol      
        var x=big.first.second
        var y=big.second
        if(x.symbol == FastNat.symbol && y.symbol == FastNat.symbol){
            var val = 0;
            var symbolFound=true
            if(symbol==plus.symbol) val = x.value + y.value
            else if(symbol==sub.symbol) {val = x.value - y.value; if(val<0) val = BigInt(0);}
            else if(symbol==times.symbol) val = x.value * y.value
            else if(symbol==divide.symbol && y!=0) val = x/y //accurate?
            else symbolFound=false
            if(symbolFound){
                //if (val==0) return zero 
                return NewFastNat(val)
            }
        }
        
    }
    //S(FastNats) = FastNats+1 //A[S,FastNat]
   // if( equiv(big , succ(X),[X] ) && RD.assigned[0].symbol==FatNat.symbol ){
    if(big.kind == "applied" && big.first.symbol==succ.symbol && big.second.symbol==FastNat.symbol){
        var val = big.second.value + BigInt(1)
        return NewFastNat(val)
    }
    if(big.symbol==Nat.zero.symbol){
        var val = BigInt(0)
        return NewFastNat(val)
    }

    //replace S(S(0)) with FASTNAT"2"
    //replace 


    if(big.kind=="applied"|| big.kind=="imply" || big.kind=="pair" || big.kind=="rule"){ //forall needed?
        var newbig = cloneInstantiated(big)
        newbig.first = ApplyFastNats(big.first);
        newbig.second =  ApplyFastNats(big.second)
        return newbig;
    }
    if(big.kind=="forall" || big.kind=="fun"){ //need checking:
        var newtype = ApplyFastNats(big.first);
        var vari=new C(getUniqueName(),newtype)
        //var newbig = cloneInstantiated(big)
        var s = ApplyFastNats(big.appliedTo(vari))
        //newbig.second =  ApplyFastNats(big.second)
        return big.kind=="forall"? FORALL(newtype,x=>REPLACE(s,vari,x)): FUN(newtype,x=>REPLACE(s,vari,x))
    }
    if(big.kind!="atom")
    print("kind not found in replace "+big.kind)
    return cloneInstantiated(big)
}

//----SHOULD WE BE CLONING TOP LEVEL TOO?

var dofc=!false



function SIMP(z, M=1, fullsimp=false){
    var topologyProps = [boundProp]
    var last=null
    z = ApplyUnappliedFunctions(z) //<---works if I put it here for some reason :s
    //alert(fullsimp)
    for(var i=0;i<M || fullsimp;i++){ //realPartRule,
        if(USE_FASTNAT)
        z= ApplyFastNats(z)
       // z=RW2(z,[sqrtSquare])

        z=RW(z,[mulOne,mulOneL,mulZero,mulZeroL,
            //timesRule,
            plusRule3,subRule,addZero , addZeroL, 
            //powerRuleT ,
            powerOneT, 
            powerZeroNat,powerZeroInt,
            factRuleN, factRule0     ,//imPartRule,
         complexARule , 
         rationalIntAddRule,//simplified
         rationalAddRule, rationalSubRule  ,intARule,intSRule, intMRule 
         ,onePower//ring
         ,qRe,qI,qJ,qK//rules of real part etc
        ])
         
        z=RW2(z,[realPartProof, imPartProof  , rationalTimesProof , rationalDivideProof,
             rationalPowerProof, complexFProof, realSeriesProp,

             powerRuleT,

             equalsT, notEqualNatL, notEqualNatR, equalNatReduce, ratEquals, intEquals

        ])
        //rings
        
        z=RW2(z,[distribL, distribR, distribLM, distribRM
        , realAddProp,realSubProp
        , realMulProp   //These go wrong with: foo=FUN(Real,x=>plusF.apply(Real,x,1));deriv.apply(foo).apply(1)
        ,RealRatPlus,RealRatTimes,

        sinSum, cosSum,
       // realToRatProp//<--illegal operation
        ])
        z=RW2(z,[
            sumProp, sumProp0,
            prodProp, prodProp0,
            iterProp, iterProp0
            ,sinPiZero,sinZero,cosZero

            ,sqrtSquare


            ,derivSin2,  derivCos2, intCos2,intSin2, derivCompos, derivPlus,derivTimes, derivConst, derivId, derivSqrt

            ,simpFunc, composeFunc
            ,makeListP,makeList0, listGet0, listGet1
            ,lt.prop, gt.prop

            ,QuaternionPlus
            //,Quaternion.times.proof
            ,QuaternionTimes

            ,eplusProp

            ,listLength1,listLength0,

            GCDRule0,gcdRule,

            zModEquals,

            natDivideRule,NatDivideRule0, toDivRoundUp,

            selectT,selectF
            ,R2ROneL, R2ROneR
            //,listFromFunc1
            //,listFromFunc0
            //ellipticPlusProp
        ])//summation rules
        if(dofc)  z=RW2(z,[ composeFunc2 ])

        z=RW2(z,topologyProps)

   //Apply any unapplied functions
   //if(window.appf)    
   //z = ApplyUnappliedFunctions(z)
//GOES WRONG due to not renaming variables???
        //iter(Nat,FUN(Nat, x=>Nat.plus(x,5)), 10,2) 

        


        if(fullsimp) {
            //var next=z.toString()
            //if(next==last) break
            var next =cloneInstantiated(z)
            if(last && equiv(next,last,[])) break;
            last=next
        }
       
    }

  

    return z
}

//window.appf=true

/*
f=FUN(Real, z=>equals.apply(Real,Sin(z),Cos(z))  )
lemma1 = Var("lemma1", f(z))
lemma2 = Var("lemma2",equals(Real, z,w))

SUBST( f, lemma1, lemma2)
*/

//This is a rule of equality //x:f(A)=f(C), y:A=B --> f(A)=f(B)

function SUBST(f, proof_fa, proofaEqB){ //A[A[A[equals,T],x],y]
    //check
    //aEqB = A(A(A(equals,F),x),y)
    var aEqB = proofaEqB.type
    if( aEqB.first.first.first.symbol!=equals.symbol){
        print(red("Not an equality: ")+aEqB)
        return
    }
    var a=aEqB.first.second
    var b=aEqB.second

    //This is not the best way to do it!!!
    if( f(a).toString() !=  proof_fa.type  ){
        print(red(normal("The proof doesn't match at "))+a+red(normal(" where ")) + f(a).toString()+ "\\neq"+  proof_fa.type  )
    }
    this.f= f
    this.proof_fa=proof_fa
    this.proofaEqB=proofaEqB
    this.symbol="SUBST"
    this.kind="subst"
    //this.type = f.apply(b)
    this.type =  f(b)//new F(proof_fa.type, new F(aEqB, f(b) ))
    //this.type = (proof_fa ^ aEqB -> fb)?
}
SUBST.prototype.toString = function(){
    //return "\\begin{bmatrix}"+this.proof_fa+"\\\\▼\\\\"+this.proofaEqB+"\\\\"+fill(this.f.toString())+"\\end{bmatrix}"
    return "\\left[\\frac{"+this.proof_fa+"◀"+this.proofaEqB+"}{"+fill(this.f.toString())+"}\\right]"
}

function Subst(a,b,c){
    return new SUBST(a,b,c)
}
//subst(Nat)(one)(one.def)(f.def)(one.proof)(two.proof)  
function Subst2(f,B,A){  //AeqB=A.def //doesn't work
    return subst(A.type,A,A.def,f,A.proof,B.proof)
}
function SubAll(Bproof, A){
    var f = match(Bproof.type, A)
    return subst(A.type,A,A.def,f,A.proof,Bproof)
}
/*
function matchOld(A,B){
    //var vari=new C(getUniqueName(),B.type)
    replacementsFound = 0
    //F=REPLACE(A,B,vari)
    var F=replaceFunc(A,B)
    if(replacementsFound ==0){
        print(red("No matches found"))
        return ErrorObject
    }
    return new Fun(B.type,F)
}*/

//------------NOT IDEAL SINCE if we embed these functions it will cause an error due to same IDS---------------------

function match(A,B,which="All"){
    var vari=new C(getUniqueName(),B.type) //Since this is unique to our new function it may be fine to use?
    replacementsFound = 0
    var RD=new ReplaceData()
    RD.which = which
    var F=REPLACE(A,B,vari,[],RD)
    if(replacementsFound ==0){
        print(red("No matches found"))
        //return ErrorObject
    }
    //why do we do it twice? (Seems like we have to)
    return FUN(B.type,x=>REPLACE(F,vari,x) )
}
/*
function match2(A,B,which="All"){
    var vari=new C(getUniqueName(),B.type) //Since this is unique to our new function it may be fine to use?
    replacementsFound = 0
    var RD=new ReplaceData()
    RD.which = which
    return FUN(B.type,x=>REPLACE(A,B,x,[],RD) )
}*/

var ABSTRACT = match;

/*
f=defineVar("f",match(two,one));
g=f(f(3));
replaceUsingEquality(g,f.proof.type)
*/



/*
f=FUN(Real, z=>equals.apply(Real,Sin.apply(z),Cos.apply(z))  )
lemma1 = Var("lemma1", f.apply(z))
lemma2 = Var("lemma2",equals.apply(Real, z,w))
new SUBST(f,lemma1,lemma2)
*/

function graph(F,xmin,xmax){
    return graphT(Real,F,xmin,xmax);
}

function insertAfter(referenceNode, newNode) {
    referenceNode.parentNode.insertBefore(newNode, referenceNode.nextSibling);
}
function removeElement(id) {
    var elem = document.getElementById(id);
    return elem.parentNode.removeChild(elem);
}

function getInput(message){
    return evalObject(eval(prompt(message)))
    //return evalObject(result)
}

///----------------------GRAPHICS----------------------

function graphT(T, F, xmin,xmax  ){
    dc = new newCanvas(W)
    W=400
    imageData = dc.getImageData(0,0,W,W)
    data = imageData.data
    clearCanvas(data,W)
    var s = (xmax-xmin)/W
    var n = new C("X",T);
    n.fastValue = ()=>window.xVal;
    n.liveVal=true;
    var Fn =  F(n);
    //console.log(fill(Fn.toString()))
    var line=true;
    if(line){
        for(var x=0;x<W;x++){
            window.xVal = xmin + x * s;
            //n.fastValue = window.xVal;
            //console.log(Fn.kind)
            var yVal = Fn.float();
            //console.log(yVal)
            var y = W-1-Math.floor(yVal/s+W/2);
            data[4*(y*W+x)] = 0
            data[4*(y*W+x)+1] = 0
            data[4*(y*W+x)+2] = 0
            data[4*(y*W+x)+3] = 255
        }
    }else{
        for(var y=0;y<W;y++){
            for(var x=0;x<W;x++){
                var yVal0 = (y-(W/2))*s
                window.xVal = xmin + x * s;
                //n.fastValue = window.xVal;
                //console.log(Fn.kind)
                var yVal = Fn.float();
                //console.log(yVal)
                //var y = Math.floor(yVal/s+W/2);
                var R = yVal < yVal0 ? 255:0
                data[4*(y*W+x)] = R
                data[4*(y*W+x)+1] = R
                data[4*(y*W+x)+2] = 255-R
                data[4*(y*W+x)+3] = 255
            }
        }
    }

    dc.putImageData(imageData,0,0)
    return 0;
}
//graph(Sin,-3,3)

//toCauchy(deriv(Real.Exp)(Real.fromRat.def(3)))(100)
//sum(Rat, FUN(Nat, n=> Rat.mk(Int.one, Int.mk( factorial(n) ,0) ) ) ,10)  

function newCanvas(W,H){
    if(!H) H=W;
    var canvas=document.getElementById(`canvas${currentID}`)
    var RATIO = window.devicePixelRatio
    //if(!canvas){
        var div = canvas?canvas:document.createElement('canvas');
        if(!canvas)div.id = `canvas${currentID}`;
        div.width=W
        div.height=H;
        div.style="border:1px black solid"
        div.style.width = W/RATIO;
        div.style.height = H/RATIO;
        if(!canvas){
        insertAfter(output,div)  
        var br =  document.createElement('br');
        insertAfter(div,br);

        canvas=document.getElementById(`canvas${currentID}`)
        }
    //}
    dc=canvas.getContext("2d")
    //fix_dpi(canvas)
    return dc
}
function clearCanvas(data,W){
    for(var x=0;x<W;x++){
        for(var y=0;y<W;y++){
            data[4*(y*W+x)] = 255
            data[4*(y*W+x)+1] = 255
            data[4*(y*W+x)+2] = 128
            data[4*(y*W+x)+3] = 255
        }
    }
}

function complexGraph(F, center, scale  ){
    W=400
    dc=newCanvas(W);
    imageData = dc.getImageData(0,0,W,W)
    if(!F.kind){
        F= FUN(CR, F );
    }

    data = imageData.data
    cx = 0
    cy = 0
    
    s = Math.PI/(W/2);
    clearCanvas(data,W)
    
    var Fn =  F.second;//F(n);

    var line=true;

    for(var y=0;y<W;y++){
        for(var x=0;x<W;x++){
            var xVal = cx + (x-W/2) * s;
            var yVal = cy + (y-W/2) * s;
            var complexVal = F.float() ( [xVal, yVal] );
            var xOut = complexVal[0];
            var yOut = complexVal[1];

            R = (Math.atan2(yOut,xOut)+Math.PI) /2
            a=1.15
            p=2
            data[4*(y*W+x)] = (Math.sin(R)**p)*255*a
            data[4*(y*W+x)+1] = (Math.sin(R + Math.PI/3)**p)*255*a
            data[4*(y*W+x)+2] = (Math.sin(R + 2*Math.PI/3)**p)*255*a
            data[4*(y*W+x)+3] = 255
        }
        
    }

    dc.putImageData(imageData,0,0)
    return 0;
}

function draw(x){
    W=400
    dc= newCanvas(W)
    imageData = dc.getImageData(0,0,W,W)
    dc.translate(W/2,W/2);
    var s=1/(Math.PI/(W/2))
    dc.scale(s,s);
    data = imageData.data
    clearCanvas(data,W)
    x.float()
}
//draw(Circle.mk(2,0,0))

mouseX=0;
mouseY=0;
time=0;
function now(){
    return new Date().getTime()/1000;
}

document.addEventListener('mousemove', function(event){
    mouseX = event.pageX/400;
    mouseY = event.pageY/400;
    time = new Date().getTime()/1000;
})

//setInterval( ()=>draw(Circle.mk(0.5,mouseX,mouseY)),200)


//scalarPlot( FUN(Real,x=>FUN(Real,y=>Real.plus(x,y) )))
function scalarPlot(F, center, scale  ){
    W=400
    dc=newCanvas(W);
    imageData = dc.getImageData(0,0,W,W)
    if(!F.kind){
        F= FUN(CR, F );
    }

    data = imageData.data
    cx = 0
    cy = 0
    
    s = Math.PI/(W/2);
    clearCanvas(data,W)
    
    var Fn =  F.second.second;//F(n);  //FUN(x,FUN(y,..))

    var line=true;

    for(var y=0;y<W;y++){
        for(var x=0;x<W;x++){
            var xVal = cx + (x-W/2) * s;
            var yVal = cy + (y-W/2) * s;
            var scalarVal = F.float() ( xVal ) (yVal);

            R = Math.atan(scalarVal)+Math.PI/2

            p=2
            data[4*(y*W+x)] = (Math.sin(R)**p)*255*a
            data[4*(y*W+x)+1] = (Math.sin(R + Math.PI/3)**p)*255*a
            data[4*(y*W+x)+2] = (Math.sin(R + 2*Math.PI/3)**p)*255*a
            data[4*(y*W+x)+3] = 255
        }
        
    }

    dc.putImageData(imageData,0,0)
    return 0;
}

function clearCanvasAll(dc,W,H,col){
    f=dc.fillStyle;
    dc.fillStyle=col;
    dc.beginPath();
    dc.rect(0,0,W,H)
    dc.fill();
    dc.fillStyle=f;
}

function plot3d( F ){
    var W=400;

    var G=40;

    dc=newCanvas(W);
    clearCanvasAll(dc,W,W,"black")


    var SC=W/G/6;
    var t=3*SC;
    var u=2*SC;
    var v=3*SC;

   
    // var Fxyz =  f.second.second.second;

    var s = 2*Math.PI/G;
    dc.fillStyle="black"
   //dc.beginPath()
        for(var x=0;x<G;x++){
            var X=(x-G/2)*s;
            for(var y=0;y<G;y++){
                var Y=(y-G/2)*s;
            for(var z=0;z<G;z++){
                var Z=(z-G/2)*s;
                var scalarVal = F.float() ( X ) (Y) (Z);
                //console.log(scalarVal)
                if(scalarVal<0){
                     dc.fillStyle="#0000FF"
                    dc.fillRect(W/2 + y*t-x*t-t, W/2.5 + x*u + y*u - z*v  ,t,u*2.5)
                    dc.fillStyle="#FF0000"
                    dc.fillRect(W/2 + y*t-x*t, W/2.5 + x*u + y*u - z*v  ,t,u*2.5)
                    dc.fillStyle="#00FF00";
                    dc.fillRect(W/2 + y*t-x*t-t, W/2.5 + x*u + y*u - z*v - u  ,t*2,u*1.5)
                }
            }
        }
    }
    //dc.fill()
    //dc.stroke()


}

function plotBitmap( C,W,H, L ,f=255){
    W0=W
    //if(C!=3) return;
    dc=newCanvas(W0);
    imageData = dc.getImageData(0,0,W,H)
    data = imageData.data
    clearCanvas(data,W)
    var n=0;
    for(var c=0;c<C;c++){
        for(x=0;x<W;x++){
            for(y=0;y<H;y++){ 
                data[ 4*(x+y*W)+c ] = L[n++]*f
            }
            //data[ 4*(w+h*W)+3 ] = 255
        }
    }
    dc.putImageData(imageData,0,0)
    return 0;
}
function drawGraph3D(M){
    return drawGraph(M,3)
}

function drawGraph(M,dim=2){ //M=Adjacenct matrix
    var N=Math.sqrt(M.length)
    var ones=0;
    for(var i=0;i<M.length;i++){
        ones+=M[i];
    }
    print(N)
    W=400
    //if(C!=3) return;
    dc=newCanvas(W);
    clearCanvasAll(dc,W,W,"white")

    var P=[] //points
    var L=[] //lines
    var V=[] //velocity


    for(var i=0;i<N;i++){
        P.push([Math.random()*W, Math.random()*W , Math.random()*W ] )
       // P.push([W/2*(1+Math.cos(i*Math.PI*2/N))  , W/2*(1+Math.sin(i*Math.PI*2/N)) ])
        V.push([0,0,0])
    }

    //create lines
    for(var i=0;i<N;i++){
        for(var j=0;j<N;j++){
            if(M[i*N+j]){
                L.push([i,j])
            }
        }
    }

    var R0 = 100;
    var dt = 1;
    var damp=0.5;
    //var k=50; //20-->10, 12-->50
    //var k=7000/(N*N);
    var k=3000/N/Math.sqrt(ones);
    //var k=4000/N / sqrt(a) // a = number of 1's per row = number of a = 4000/sqrt{number of 1's}

    for(var t=0;t<1000;t++){
        for(var i=0;i<P.length;i++){
            for(var j=0;j<P.length;j++)if(i!=j){
                var P0=P[i];
                var P1=P[j];
                var DX = -(P0[0]-P1[0]);
                var DY = -(P0[1]-P1[1]);
                var DZ = dim<=2?0:-(P0[2]-P1[2]);
                var R2 = Math.sqrt(DX*DX+DY*DY + DZ*DZ)
                
                V[i][0]+=  (-DX/R2/R2*k + M[i*N+j]*DX/R2)*dt;
                V[i][1]+=  (-DY/R2/R2*k + M[i*N+j]*DY/R2)*dt;
                V[i][2]+=  (-DZ/R2/R2*k + M[i*N+j]*DZ/R2)*dt;
            }
        }

        for(var j=0;j<dim;j++){
            for(var i=0;i<P.length;i++){
                P[i][j]+=  V[i][j]*dt;
                V[i][j]*=damp;
            }
        }
    }
        //draw 
        dc.beginPath()
        for(var l=0;l<L.length;l++){
            var P0=P[L[l][0]];
            var P1=P[L[l][1]];
            dc.moveTo(P0[0],P0[1]);
            dc.lineTo(P1[0],P1[1]);
        }
        dc.stroke()
    

}





var nodeList=[]
var edgeList=[]
var offsets=[]
var variDict={}
function getNodeList(exp,parent,L){
   // if(L>50) return;
    //if(nodeList.includes(exp)) return;
    if(!exp) {
        console.log("exp undefined");
        return;
    }
    if(L>=offsets.length)offsets.push(0)
    var AL=false;
    if(exp.kind=="applied") {
        exp = toAppliedList(exp)
        console.log(exp)
        AL=true;
    }
    if(exp.kind=="AL") AL=true;
    var isNew = !nodeList.includes(exp);
    if(isNew){
        exp.x = Math.floor((offsets[L])*50*scale)
        exp.y = Math.floor(L*50*scale)
        if(exp.symbol[0]=="@") {
            exp.color="pink";
            variDict[exp.symbol] = getSimpleVariName();
        }
        nodeList.push(exp)
        offsets[L]++;
        exp.xID=offsets[L];
        exp.yID=L;
    }
    if(parent) edgeList.push([parent,exp]);
    if(!isNew) return;
    if(exp.kind=="fun" || exp.kind=="forall"){
        getNodeList(exp.vari,exp,L+1)
    }else
    if(exp.first){
        if(exp.first.kind=="atom" && AL) exp.symbol = exp.first.symbol;
        else getNodeList(exp.first,exp,L+1)
    }
    if(exp.second) {
        if(AL){for(var i=0;i<exp.second.length;i++) getNodeList(exp.second[i],exp,L+1)}
        else getNodeList(exp.second,exp,L+1)
    }
}





/*
function fix_dpi(canvas) {
    dpi = window.devicePixelRatio;
//create a style object that returns width and height
  let style = {
    height() {
      return +getComputedStyle(canvas).getPropertyValue('height').slice(0,-2);
    },
    width() {
      return +getComputedStyle(canvas).getPropertyValue('width').slice(0,-2);
    }
  }
//set the correct attributes for a crystal clear image!
  canvas.setAttribute('width', style.width() * dpi);
  canvas.setAttribute('height', style.height() * dpi);
}*/
var scale = 1;

function eqGraph(exp){
    scale=1.25 * window.devicePixelRatio;
    nodeList=[]
    edgeList=[]
    offsets=[]
    
    getNodeList(exp,null,0)
    //console.log("DONE");return;
    var maxX = Math.max(...offsets)
    //space them out
    for(var i=0;i<nodeList.length;i++){
        A = nodeList[i]
        A.x = Math.floor( (maxX * 50 / 2 + (A.xID-0.5 - offsets[A.yID]/2) * 50)*scale);
        //A.x = Math.floor((A.xID-0.5) *  ( maxX * 50 / offsets[A.yID] )*scale)
    }

    var W = Math.floor((maxX * 50+25) * scale)
    var H = Math.floor(((offsets.length-1) * 50+25)*scale)
    //if(C!=3) return;
    dc=newCanvas(W,H);
    dc.resetTransform()
    clearCanvasAll(dc,W,H,"white")
    console.log("nodes",nodeList.length);
    console.log("edges",edgeList.length)

    
    //draw nodes
    var s=Math.floor(7*scale)+0.5;
    var t=Math.floor(21*scale)+0.5;
    var k=Math.floor(40*scale);

    //console.log(scale)

    dc.font = Math.floor(10*scale)+"px Arial";

    dc.translate(25,25)
    dc.lineWidth = 1;
    //edges
    dc.beginPath();
    for(var i=0;i<edgeList.length;i++){
        var C =edgeList[i];
        dc.moveTo(C[0].x, C[0].y)
        //dc.lineTo(C[1].x, C[1].y)
        dc.bezierCurveTo(C[0].x, C[0].y+k,C[1].x, C[1].y-k,C[1].x, C[1].y)
    }
    dc.stroke();   

    dc.fillStyle="yellow";
    //dc.beginPath();
    for(var i=0;i<nodeList.length;i++){
        var A=nodeList[i];
        dc.fillStyle= A.color?A.color:(A.symbol=="FastNat"?"orange":"yellow");
        dc.fillRect(A.x-t, A.y-s,t*2,2*s)
        dc.strokeRect(A.x-t, A.y-s,t*2,2*s)
    }
    //dc.fill();
    //dc.stroke();
    dc.textAlign = "center";
    dc.textBaseline = "middle"
    dc.fillStyle="black";
    dc.beginPath();
    for(var i=0;i<nodeList.length;i++){
        var A=nodeList[i];
        var s=A.symbol=="FastNat"?A.value:(A.symbol[0]=="@"?variDict[A.symbol]: A.symbol);
        //var t=A.kind=="AL"?A.getTypeInputForm():A.type.inputForm();
        //dc.fillText(s+":"+t,A.x,A.y)
        dc.fillText(s,A.x, A.y )
    }
    dc.fill();

//test
/*
var tex = "\\frac{2}{3}";
console.log(MathJax)
var svg = MathJax.tex2svg(tex);
var svg = svg.childNodes[0]
var ssvg = new XMLSerializer().serializeToString(svg);
var base64 = "data:image/svg+xml;base64, " + window.btoa(unescape(encodeURIComponent(ssvg)));
*/
}

//eqGraph(ComplexMk(Rat)(2,3.5))



function playAudio(floatList) {
    // Your float array data
    const floatArray = new Float32Array(floatList);

    // Create an audio context
    const audioContext = new (window.AudioContext || window.webkitAudioContext)({
        sampleRate: 22050
    });

    // Create an audio buffer
    console.log("Samplerate" , audioContext.sampleRate)
    const audioBuffer = audioContext.createBuffer(1, floatArray.length, audioContext.sampleRate);

    // Fill the buffer with the float array data
    audioBuffer.copyToChannel(floatArray, 0, 0);

    // Create a buffer source node
    const source = audioContext.createBufferSource();
    source.buffer = audioBuffer;

    // Connect the source to the context's destination (the speakers)
    source.connect(audioContext.destination);

    // Start the source
    source.start();
}

//Replace everything with it's definition

function finddef(A){
    if(A.def!=undefined) return A
    if(A.first){
        var F=finddef(A.first)
        if(F!=null) return F
    }
    if(A.second){
        var S=finddef(A.second)
        if(S!=null) return S
    }
    return null
}

function DEFEVAL(A){
    var R=A
    var B;
    var i=0;
    while((B=finddef(R)) && i<10000){
        //console.log(i+"Found :" + fill(B.toString()))
        R = REPLACE(R,B,B.def)
        i++;
    }
    R= ApplyUnappliedFunctions(R); //<--should do this multiple times
    return R;// REBUILD(R) //<--rebuild causes problems here!!!
}
 

function DEFEQUIV(A,B){ 
    var A2=DEFEVAL(A)
    var B2=DEFEVAL(B)
    return equiv(A2,B2)
}



function vectorPlot(T, F, xmin,xmax, ymin, ymax  ){
    W=400
    dc = new newCanvas(W)

    imageData = dc.getImageData(0,0,W,W)
    data = imageData.data
    clearCanvas(data,W)
    var s = (xmax-xmin)/W
    var n = new C("X", Vector(T,2));
    n.fastValue = ()=>window.xVal;
    n.liveVal=true;
    var Fn =  F(n);
    //console.log(fill(Fn.toString()))
    var line=true;
    var step=20;

    for(var y=0;y<W;y+=step){
        for(var x0=0;x0<W;x0+=step){
            var x=x0 ;//+ ((y%(2*step)==0)?(step/2):0);
            var yVal0 = (y-(W/2))*s
            window.xVal = [xmin + x * s, ymin+y*s];
            //n.fastValue = window.xVal;
            //console.log(Fn.kind)
            var result = Fn.float();
            var x2=result[0];
            var y2=result[1];
            var mag=Math.sqrt(x2*x2+y2*y2)
            if(mag>0.00001){
            x2*=step/mag/2;
            y2*=step/mag/2;
            }
            
            dc.beginPath()
            dc.moveTo(x-x2,y-y2)
            dc.lineTo(x+x2,y+y2)
            dc.stroke()
        }
    }

    return 0;
}