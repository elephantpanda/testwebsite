var USE_MATHJAX=true
var DARK_MODE=true
var USE_FASTNAT=true 
var DEBUG_MODE=true
var SHOW_LONG_NATS=!true
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
    <button onclick="go(${inputID},true)">Eval</button>
    <button onclick="fullsimplify('output${inputID}')">SIMP</button>
    <button onclick="simplify('output${inputID}')">SIMP ONCE</button>
    <button onclick="tofloat('output${inputID}')">TO FLOAT</button>
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
      output.innerHTML+=key+"<br>"
    }
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
var result=null

function fill(f){
    while(typeof f=='function'){
        f= f("■")
    }
    return f
}

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

        if(result!=null){
            if(typeof result==='number') {
                result = guessNumberType(result)   
            }
            if(result instanceof Array){    
                result = toList(result)
            }
            var type=result.type
            if(type==undefined)
                print(normal(result.toString()))
            else
                print(fill(result.toString()) + " : " +fill(result.type.toString()))
        }
    }

    if(window.MathJax!=undefined)
    MathJax.typesetPromise([output]).then(() => {
        //console.log("Typesetting complete.");
    }).catch((err) => console.error(err.message));

    //MathJax.typeset()
}
function guessNumberType(result){
    if(result!=Math.floor(result)) return toRat(result)
    else if(result<0 ) return toInt(result ) 
    else return N(result)    
}
function toList(list ,type=null){
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
}
function LIST(...args){
    return toList(args)
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

function tofloat(outputName){  
    output=document.getElementById(outputName)
    result = result.float()
    output.innerHTML+=result
}

function simplify(outputName){  
    output=document.getElementById(outputName)
    result = SIMP(result)
    print(fill(result.toString()) + " : " +result.type)
    MathJax.typeset()
}
function jax(x){
    if(USE_MATHJAX) return "\\("+x+"\\)"
    else return x
}

function fullsimplify(outputName){  
    output=document.getElementById(outputName)
    result = SIMP(result,M=1,fullsimp=true)
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

function C(a,t){
    const inst = function(...args){
        return inst.apply(...args);
    }
        
    //const instance=this
    inst.symbol = a
    inst.type = t
    inst.kind = "atom"
    inst.postfix=false
    inst.bold=false
    inst.notation=a

    Object.setPrototypeOf(inst, C.prototype)

    return inst
}

C.prototype.apply=function(...args){
    var N=this
    for(var i=0;i<args.length;i++){
        N = APPLY(N,args[i])
        //N = apply(N,args[args.length-1 -i])
    }
    return N
}
C.prototype.to = function(x){
    return new F(this,x)
}
C.prototype.float = function(){
    if(FastNat && this.symbol==FastNat.symbol) return Number(this.value);
    if(this.liveVal) return this.fastValue();
    else
    return this.fastValue
}

C.prototype.toString = function(){    
    if(this.symbol=="?"){
        if(wilds[this.value]) return wilds[this.value].toString()
    }
    if(this.notation!=null)return this.notation
    if(this.bold) return red(bold(this.symbol)); 
    return this.symbol
 }
 C.prototype.by = function(f){
    return f(this);
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
    return result
}

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
    return a
}
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
var Type1=new C(orange("\\mathscr{T}"),Type2)
var Type=new C(orange("\\mathscr{T}"),Type1)

var ErrorMessage =new C(red("ERROR"),Type)
var ErrorObject = new C(red("⚠"),ErrorMessage)

var Prop= new C(pink("Prop"),Type)

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




function Applied(a,b,t){
    const inst = function(...args){
        return inst.apply(...args);
    }

    inst.first=a;
    inst.second=b;
    inst.type=t
    inst.kind="applied"
    inst.posfix=false;
    inst.notation=null

    Object.setPrototypeOf(inst, Applied.prototype)
    return inst
}

Applied.prototype.to = function(x){
    return new F(this,x)
}

Applied.prototype.apply=function(...args){
    var N=this
    for(var i=0;i<args.length;i++){
        N=APPLY(N,args[i])
    }
    return N
}
Applied.prototype.by = function(f){
    return f(this);
}

Applied.prototype.float = function(){
    var firstValue = this.first.float()
    var secondValue = typeof this.second.float=='function'? this.second.float() : null
   // if(!firstValue) console.log("No getFast on" + fill(this.first.toString())+" "+this.first.kind)
   // if(!secondValue) console.log("No getFast on" + fill(this.second.toString())+" "+this.second.kind)
   if(typeof firstValue!='function'){
        //console.log(fill(this.first.toString())+" not a function  ")
        return null
   }
   //console.log(this.kind+","+this.second.kind+" "+this.second.symbol+" ("+secondValue+")")
    return firstValue(secondValue);
}

Applied.prototype.fastValue = function(){
    console.log("HELLO")
}

Applied.prototype.toString = function(){
    if(this.notation) return this.notation
    var firstString = this.first.toString()
    var secondString = this.second.toString()
    if(typeof firstString =='function') return firstString(secondString, this.second)
    

   if(this.first.postfix)
        return  (this.second.kind=="applied"?"("+ secondString+")" : secondString+" "  ) + this.first
   else {
    if(this.first.kind!="fun")
    return firstString+ "("+ fill(secondString)+")" ;
else
return "("+firstString+ ")("+ fill(secondString)+")" ;
    //return firstString+ (this.second.kind=="applied"?"("+ secondString+")" :" "+ secondString  )
   }
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
        this.type = this.second ? this.second.type : null //inherits type?//f(x).type
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
        if (USE_MATHJAX) return "\\bigwedge\\limits_{" + tempVari + "\\in " + this.first + "}" + fill(second.toString())
        return red(bold("∀")) + "(" + tempVari + ":" + this.first + ")," + fill(second.toString())
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
        inst.symbol = "??"

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
    else  if(A.symbol==Int.symbol) b = toInt(b)
    else  if(A.symbol==Rational.symbol) b = toRat(b)
    else if(A.symbol==Real.symbol) b=toReal(b)
    else if( equiv(A, R2R) ) b=toConstFunc(b)
    else if(A.kind=="applied"){
        if(A.first.symbol == Zmod.symbol) b= Zmod.fromNat( A.second,b)       
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
    if(b instanceof BigInt){
        var result = new Var(FastNat.symbol,Nat)
        result.notation = "["+b+"]"+subscript("ℕ")
        result.value = b
        b=result
    }

    //fast check first?
    if ( !equiv(expectedType,b.type)){
    //if(expectedType.toString()!=b.type.toString()){
    //if(a.type.first != b.type) {  //   :N->M
        //SHOULD CHECK DEFINITIONAL EQUALITY!//

        if(! defEqual( expectedType,b.type) ){

        var warning=red(normal("⚠"))+fill(a.toString())+red(normal(" expected ■ : "))+fill(expectedType.toString()) +red(normal("  Got "))+fill(b.toString()) + " : "+b.type
        console.log(warning)
        print(warning);
        print(blue(normal("(Need to implement definitional equality check)")))
        if(USE_MATHJAX) MathJax.typeset();
        b = ErrorObject
        //return null;
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
    n=n>=0?n:0
    if(USE_FASTNAT){
        if(n==0) return zero;
        if(n==1) return one;
        else 
        {
            var result = new Var(FastNat.symbol,Nat)
            result.notation = fastNatNotation(n)
            result.value = BigInt(n)
            return result
        }
    }
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

function toRat(n){
    var sign=1;
    if(n<0) { n=-n; sign=-1;}
    if(Math.floor(n)==n) return RationalMk.apply(sign*n,1)
    else {
        var den = Math.pow(10,n.countDecimals())
        var num = Math.floor(n*den+0.5)
        var GCD = (num>den)? gcd(num,den) : gcd(den,num)
        return RationalMk.apply( sign*(num/GCD),den/GCD)
    }
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


function equiv(a,b, varis=[], RD=new ReplaceData(), fastnatcount=0){ 

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
    if(false) //need to update replace
    if(FastNat!=undefined && succ!=undefined && (a.symbol==FastNat.symbol || b.symbol==FastNat.symbol)){
        if(b.symbol==FastNat.symbol){ 
            if(a.symbol==FastNat.symbol) return b.value+fastnatcount==a.value
            if(a.symbol == zero.symbol) return b.value+fastnatcount==0
            if( a.kind=="applied" && a.first.symbol==succ.symbol){ 
                if( b.value==0 ) return false
                return equiv(a.second,b, varis,RD, fastnatcount-1 )
            }
            return false
        }
        if(a.symbol==FastNat.symbol){  
            if(b.symbol == FastNat.symbol)return a.value-fastnatcount==b.value
            if(b.symbol == zero.symbol) return a.value-fastnatcount==0        
            if(b.kind=="applied" && b.first.symbol==succ.symbol){ 
                if(a.value==0) return false 
                return equiv(a,b.second, varis,RD, fastnatcount+1 )        
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
    if(equiv(big,small, varis,RD)) {
        replacementsFound ++
        return newterm; //<----Let's not clone it. Will this be problem???
        //cloneInstantiated(newterm) //<--- do replacement here???
    }else RD.assigned=temp
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
        print("kind not found in replace "+big.kind +" "+fill(big.toString()))
    return cloneInstantiated(big)
}


function findMatch(big, small, newterm ,varis=[]){  //, RD.assigned=[]
    var temp = RD.assigned.slice()
    if(equiv(big,small)){//, varis,RD)) {
        return true
    }else RD.assigned=temp
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

        var resultType= REPLACE(big.type, root.first, root.second, varis,RD)

        for(var i=0;i<varis.length;i++){
            result = REPLACE(result,varis[i] , RD.assigned[i] )
            resultType = REPLACE(resultType,varis[i] , RD.assigned[i] )
        }
        result.type= resultType
    }//else result = big

    return result
}

function replaceUsing2(big, rule){
    
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
    
    if(RD.assigned.length==0 || !RD.assigned.includes(null) ){        
        var resultType= REPLACE(big.type, x,y, varis, RD)
        for(var i=0;i<varis.length;i++){
            result = REPLACE(result,varis[i] , RD.assigned[i] )
            resultType = REPLACE(resultType,varis[i] , RD.assigned[i] )
        }
        result.type= resultType
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
        big = replaceUsing2(big,rules[i].type)
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
        return APPLY(big.first,big.second)
    }
    if(big.kind=="applied"|| big.kind=="imply" || big.kind=="pair" || big.kind=="rule"){ //forall needed?
        var newbig = cloneInstantiated(big)
        newbig.first = ApplyUnappliedFunctions(big.first);
        newbig.second =  ApplyUnappliedFunctions(big.second)
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
            else if(symbol==sub.symbol) val = x.value - y.value
            else if(symbol==times.symbol) val = x.value * y.value
            else if(symbol==divide.symbol) val = Math.floor(x/y) //accurate?
            else symbolFound=false
            if(symbolFound){
                if (val==0) return zero
                var result = new Var(FastNat.symbol, Nat)
                result.value = val
                result.notation = fastNatNotation(val)
                return result
            }
        }
        
    }
    //S(FastNats) = FastNats+1 //A[S,FastNat]
   // if( equiv(big , succ(X),[X] ) && RD.assigned[0].symbol==FatNat.symbol ){
    if(big.kind == "applied" && big.first.symbol==succ.symbol && big.second.symbol==FastNat.symbol){
        var val = big.second.value + BigInt(1)
        var result = new Var(FastNat.symbol, Nat)
        result.value = val
        result.notation = fastNatNotation(val)
        return result
    }
    if(big.symbol==Nat.zero.symbol){
        var val = BigInt(0)
        var result = new Var(FastNat.symbol, Nat)
        result.value = val
        result.notation = fastNatNotation(val)
        return result
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
    //alert(fullsimp)
    for(var i=0;i<M || fullsimp;i++){ //realPartRule,
        if(USE_FASTNAT)
        z= ApplyFastNats(z)
       // z=RW2(z,[sqrtSquare])

        z=RW(z,[mulOne,mulOneL,mulZero,mulZeroL,timesRule,plusRule3,subRule,addZero , addZeroL, powerRuleT ,powerOneT, factRuleN, factRule0     ,//imPartRule,
         complexARule , 
         rationalAddRule, rationalSubRule  ,intARule,intSRule, intMRule 
         ,onePower//ring
         ,qRe,qI,qJ,qK//rules of real part etc
        ])
         
        z=RW2(z,[realPartProof, imPartProof  , rationalTimesProof , rationalDivideProof,
             rationalPowerProof, complexFProof, realSeriesProp

        ])
        //rings
        
        z=RW2(z,[distribL, distribR, distribLM, distribRM
        , realAddProp,realSubProp
        , realMulProp   //These go wrong with: foo=FUN(Real,x=>plusF.apply(Real,x,1));deriv.apply(foo).apply(1)
        ,RealRatPlus,RealRatTimes,

        sinSum, cosSum
        ])
        z=RW2(z,[
            sumProp, sumProp0,
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

            //,listFromFunc1
            //,listFromFunc0
            //ellipticPlusProp
        ])//summation rules
if(dofc)  z=RW2(z,[ composeFunc2])

        z=RW2(z,topologyProps)

   //Apply any unapplied functions
        z = ApplyUnappliedFunctions(z)
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

function match(A,B){
    var vari=new C(getUniqueName(),B.type) //Since this is unique to our new function it may be fine to use?
    replacementsFound = 0
    var F=REPLACE(A,B,vari)
    if(replacementsFound ==0){
        print(red("No matches found"))
        //return ErrorObject
    }
    return FUN(B.type,x=>REPLACE(F,vari,x) )
}

/*
f=defineVar("f",match(two,one));
g=f(f(3));
replaceUsing2(g,f.proof.type)
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

function newCanvas(W){
    var canvas=document.getElementById(`canvas${currentID}`)

    if(!canvas){
        var div = document.createElement('canvas');
        div.id = `canvas${currentID}`;
        div.width=W
        div.height=W
        div.style="border:1px black solid"
        insertAfter(output,div)  
        canvas=document.getElementById(`canvas${currentID}`)
    }
    dc=canvas.getContext("2d")
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

function clearCanvasAll(dc,W,col){
    f=dc.fillStyle;
    dc.fillStyle=col;
    dc.beginPath();
    dc.rect(0,0,W,W)
    dc.fill();
    dc.fillStyle=f;
}

function plot3d( F ){
    var W=400;

    var G=40;

    dc=newCanvas(W);
    clearCanvasAll(dc,W,"black")


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

function plotBitmap( C,W,H, L ){
    W0=400
    //if(C!=3) return;
    dc=newCanvas(W0);
    imageData = dc.getImageData(0,0,W,H)
    data = imageData.data
    clearCanvas(data,W)
    var n=0;
    for(var c=0;c<C;c++){
        for(x=0;x<W;x++){
            for(y=0;y<H;y++){ 
                data[ 4*(x+y*W)+c ] = L[n++]*255
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
    clearCanvasAll(dc,W,"white")

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