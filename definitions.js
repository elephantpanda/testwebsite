/*

 Here we define the mathematical definitions

*/

/*
def ONE:=Nat.succ Nat.zero
def TWO:=Nat.succ ONE

def proofA: Nat.succ TWO = Nat.zero.succ.succ.succ := by
rw [TWO]
rw [ONE]

#print proofA
And the output of the proof is:

def proofA : TWO.succ = Nat.zero.succ.succ.succ :=
Eq.mpr (id (congrArg (fun _a => _a.succ = Nat.zero.succ.succ.succ) TWO.eq_1))
  (Eq.mpr (id (congrArg (fun _a => _a.succ.succ = Nat.zero.succ.succ.succ) ONE.eq_1)) (Eq.refl Nat.zero.succ.succ.succ))
So it looks like the rewrite rules are written like for replacing P(b) with P(c) given b=c:




Eq.mpr (id (congrArg (fun _a => P(_a) ) c))
which unfortunately would be a bit of a long way to write it if you needed to just substitute one variable in a really big expression because first you'd have to write your expression in the form P(a)
*/

//ELEMENTS
/*
*ATOMS* (Types)
A : b->c->d->e : Type
plus: Nat->Nat->Nat :Type



*Rules (Props)*
proof1: ForAll (A,B,C $X$, E,E   ) : Prop


**Pseudonyms* [LHS can be replaced by RHS]
two = zero.succ.succ
square = FUN(x=>Nat.times(x,x)) 
*/


// Fields Nat, Rational, Int, Complex, Quaternion, Octonion


var Nat = AXIOM("ℕ",Type); Nat.fastValue=Nat; Nat.notation = blue("ℕ");
var zero = Nat.zero = AXIOM(0,Nat); Nat.zero.notation = SHOW_LONG_NATS?"0":0; Nat.zero.fastValue=0;
var succ = Nat.succ = AXIOM("S", Nat.to(Nat)) ; succ.notation = x=> ( typeof x ==='number'? 1+x : "("+red(bold("S"))+x+")"   ); succ.fastValue = x=>1+x;
var x = AXIOM("x", Nat)
var y = AXIOM("y", Nat)
var one = succ(zero)
var two = APPLY(succ, one)
var three = APPLY(succ, two)
var four = APPLY(succ, three)

var FastNat = AXIOM("FastNat",Nat)
fastNatNotation = function(val){
    if(SHOW_LONG_NATS && false){
        var s="0"
        for(var i=0;i<val;i++){
            s="("+red(bold("S"))+s+")"
        }
        return s
    }

    return val
    //return "["+val+"]"//+subscript("ℕ")
}


/*
function defFun(name, f, argTypes ){
     var header =  AXIOM(name, f.type)
      AXIOM("def_"+name, FORALL(argTypes[0],x=>FORALL( argTypes[1], y=>equals( variable.type, header(x,y ),   f(x,y) ) ) ))
     return f
}*/

function isNumber(x){
    return (typeof x == 'number') ||  (typeof x =='bigint');
}

var Int = AXIOM("ℤ",Type) ; Int.notation = blue("ℤ")
var IntMk = Int.mk= AXIOM("ℤ.mk", Nat.to(Nat.to(Int))) ; Int.mk.fastValue = x=>y=>(x-y);
IntMk.notation = x=>y=>{
    if( isNumber(x) && isNumber( y)) return (BigInt(x)-BigInt(y))
    else if(x==0 && y==0) return "0"
    else if (x==0) return "-"+y+""
    else if (y==0) return ""+x+""
    else return "("+x+"-"+y+")"
}

Int.zero = IntMk(0,0)
Int.one = IntMk(1,0)
Int.minusOne = IntMk(0,1)





var Complex = AXIOM("ℂ",Type.to(Type)); //--struct
Complex.notation = type=>blue("ℂ")+"["+type+"]"; Complex.fastValue =  x=>"C["+x+"]";
var ComplexMk = Complex.mk = AXIOM("ℂ.mk", new ForAll( new C(cal("F"),Type) , F=>F.to( F.to(Complex(F)))))
ComplexMk.notation = type=>x=>y=> "("+x+" + " + y + (bold("i"))+")"//   + subscript(type)
Complex.mk.fastValue = t=>x=>y=>[x,y]
//Do I have to define it as Complex(Cos()+iSin())??
// or   (f=>Complex(Real)( Re(f) , Im(f)  )(  n=> Complex(Rational)(n) )


var Quaternion = AXIOM("ℍ",Type.to(Type)) //--struct //H[Nat]
Quaternion.notation = type=>blue("ℍ")+"["+type+"]"

var QuaternionMk = Quaternion.mk = AXIOM("ℍ.mk", new ForAll( new C(cal("F"),Type) , F=> (F.to(F.to(F.to(F.to( Quaternion(F)   )))))))
QuaternionMk.notation = type=>re=>i=>j=>k=>"("+re+"+"+i+bold("I")+"+"+j+bold("J")+"+"+k+bold("K")+")"+subscript(type)
Quaternion.mk.fastValue = t=>x=>y=>z=>w=>[x,y,z,w];

var Octonion = AXIOM("𝕆",Type.to(Type)) //--struct
Octonion.notation = type=>blue("𝕆")+"["+type+"]"
var OctonionMk = AXIOM("𝕆.mk", new ForAll( new C(cal("F"),Type) , F=>F.to(F.to(F.to(F.to(F.to(F.to(F.to(F.to( Octonion(F)  ))))))))))
OctonionMk.notation = type=>re=>e1=>e2=>e3=>e4=>e5=>e6=>e7=>"("+re+"+"+e1+QE(1)+"+"+e2+QE(2)+"+"+e3+QE(3)+"+"+e4+QE(4)+"+"+e5+QE(5)+"+"+e6+QE(6)+"+"+e7+QE(7)+")"


// --------------------RATIONAL----------------------------


var Rat = Rational = AXIOM("ℚ",Type) ;Rat.fastValue="Q"; Rat.notation = blue("ℚ")
var RatMk =Rat.mk = RationalMk = AXIOM("ℚ.mk", Int.to(Int.to(Rational)))  ; Rat.mk.fastValue = x=>y=>Number(x)/Number(y);
Rat.one =  RationalMk(1,1)
Rat.zero = RationalMk(0,1)

Rat.fromInt = FUN(Int,x=>Rat.mk(x,1))
Rat.fromNat = FUN(Nat,n=>Rat.mk(Int.mk(n,0),1))

var PosRat= AXIOM(blue("ℚ^{+}"),Type) 
var PosRatMk = PosRat.mk = PosRatMk = AXIOM("/", Nat.to(Nat.to(PosRat)))
PosRat.one =  RationalMk(1,1)
PosRat.zero = RationalMk(0,1)

//ComplexMk(Real)( Real.zero , Pi  )


//var RationalMk = AXIOM("/", Int.to(Nat.to(Rational)))
Rat.mk.notation = x=>y=>{
    if(y==1) return x+subscript(blue("ℚ"));
    else return "\\frac{"+x+"}{"+y+"}"
}
PosRat.mk.notation = x=>y=>{
    if(y==1) return x+subscript(blue("ℚ^{+}"));
    else return "\\frac{"+x+"}{"+y+"}"
}





var Algebraic = AXIOM("Algebraic", Type)

//-------------------BINARY------------------
var Bin = AXIOM(blue("Bin"),Type )
Bin.zero = AXIOM("b",Bin);Bin.zero.notation="b"                   ;Bin.zero.fastValue = 0;
var Bit1 = AXIOM("b1",Bin.to(Bin)); Bit1.notation = x=>x+"1"      ;Bit1.fastValue = x=>2*x+1;
var Bit0 = AXIOM("b0",Bin.to(Bin)); Bit0.notation = x=>x+"0"      ;Bit0.fastValue = x=>2*x;





var Sqrt =AXIOM("Sqrt[ℕ]",Nat.to(Type))


var SqrtMk = AXIOM("SqrtMk", Nat.to(Sqrt))
SqrtMk.notation = x=> {
    if(USE_MATHJAX) return "\\sqrt{"+x +"}"
    else return "√("+x+")"
}

function getName(x){
    for(o in window){ 
        if(window[o] === x){
            return o
        }
    }
}


//-------------tests------------------

// rule = F:N->P  <=> forall (F): ForAll (N->p) //forall: Nat->Prop->ForAll (N->Prop)???
var complex3_4 = ComplexMk(Nat,3,4)
var rational2_3 = RationalMk(2,3)
var quaternion1234 = QuaternionMk(Int,1,2,3,4)
var quaternionRat = QuaternionMk(Rational,RationalMk(2,3),RationalMk(1,3),RationalMk(4,5),RationalMk(6,7))
var complexQuat = QuaternionMk(Complex(Nat),ComplexMk(Nat,2,3) ,ComplexMk(Nat,2,3),ComplexMk(Nat,2,3),ComplexMk(Nat,2,3) )
var sqrt_2 = SqrtMk(two)
var one_two = new P(one,two)
var one_two_three = new P(one_two,three)
var Nat_Nat = new P(Nat,Nat)
var NatToNatToNat =Nat.to(Nat.to(Nat))
var NatToNatToProp =Nat.to(Nat.to(Prop))

// ----------------------Field operators----------------------

var plus = AXIOM("+", FORALL(Type, F=>F.to(F.to(F)) ));  plus.notation=type=>x=>y=>"("+fill(x)+"+"/*+subscript(type)*/+""+fill(y)+")"
var times = AXIOM("×", FORALL(Type, F=>F.to(F.to(F)) )); times.notation=type=>x=>y=>"("+fill(x)+"×"/*+subscript(type)*/+""+fill(y)+")"
var sub = AXIOM("-", FORALL(Type,F=>F.to(F.to(F))  ));   sub.notation=type=>x=>y=>"("+fill(x)+"-"/*+subscript(type)+""*/+fill(y)+")"
var divide = AXIOM("/", FORALL(Type,F=>F.to(F.to(F))  ));divide.notation=type=>x=>y=>"\\frac{"+fill(x)+"}{"/*+subscript(type)*/+""+fill(y)+"}"

times.fastValue = t=>x=>y=>x*y;
sub.fastValue = t=>x=>y=>x-y;
divide.fastValue = t=>x=>y=>x/y;
plus.fastValue = t=>x=>y=>x+y;

times.fastValue = t=>x=>y=>{
    //if(t.fastTimes) return t.fastTimes(x,y);
    //if(t.kind=="applied" && t.first.fastTimes) return t.first.fastTimes(t.second.float())(x)(y) //SLOWER!!!
    return x*y;
}




//helprt function
//var PLUS=x=>y=>plus(x.type,x,y)

//var plus3=T=>x=>y=>z=>plus(T,plus(T,x,y),z)
var plus3=FUN(Type,T=>FUN(T,x=>FUN(T,y=>FUN(T,z=>plus(T,plus(T,x,y),z)))))
var plus4=T=>x=>y=>z=>t=>plus(T,plus3(T,x,y,z),t)

var square = FUN(Type,F=>FUN(F, x=> times(F,x,x)   ))


var power = AXIOM("^",FORALL(Type,F=>F.to(Nat.to(F))  )); power.notation = type=>x=>y=>"\\left("+x+"\\right)^{"+y+"}"; power.fastValue = t=>x=>y=>Math.pow(x,y);

//-------------real-------------------
var R = Real = AXIOM("ℝ",Type); Real.fastValue=Real; Real.notation =blue("ℝ")  //"R";
//Real = Cauchy series: {F[i]}
Real.mk = AXIOM("R.mk", Nat.to(Rational).to(Real) ) /*plus proof of convergence?*/
Real.mk.notation = (x,y)=>{  
    //---need to only return [A] value if is is wholy numeric without any variables
    /*if(y && y.kind=="fun"){
        //(A A RationalMk 1 3)
        if(y.second.kind=="applied" && y.second.first.kind=="applied" &&  y.second.first.first.symbol==RationalMk.symbol){
            return "("+y.second+")"+subscript("ℝ")
        }
        return "["+y.second.type+" "+y.second.first.type+" "+y.second.first.first.symbol+"]"
    }else*/
    if(y && y.kind=="fun"){
        var vari=new C(getNewVariName(),y.vari.type)
        return "\\lim\\limits_{"+vari+"\\rightarrow \\infty} \\left\\{" + y.appliedTo(vari) +"\\right\\}"  //y.vari, y.second
    }else
    return "\\lim \\left\\{" + x +"\\right\\}" 
}

Real.mk.fastValue = (x,y)=>{
    //print(blue(normal("(Taking the 100th term)")))
    //MathJax.typeset()
    return y.float(0)(100);
}

//for machine learning???
var Bool = AXIOM("bool",Type); Bool.notation=blue("\\mathbb{B}")

var Float16 = AXIOM("f16",Type); Float16.notation=blue("\\mathbb{f16}")
var Float32 = AXIOM("f32",Type);Float32.notation=blue("\\mathbb{f32}")
var Float64 = AXIOM("f64",Type); Float64.notation=blue("\\mathbb{f64}");//Float64.mk = AXIOM("Float64mk",Float64); Float64.mk.fastValue = ()=>

var UInt8 = AXIOM("u8",Type); UInt8.notation=blue("\\mathbb{u8}")
var UInt16 = AXIOM("u16",Type); UInt16.notation=blue("\\mathbb{u16}")
var UInt32 = AXIOM("u32",Type); UInt32.notation=blue("\\mathbb{u32}")
var UInt64 = AXIOM("u64",Type); UInt64.notation=blue("\\mathbb{u64}")

var Int8= AXIOM("i8",Type); Int8.notation=blue("\\mathbb{i8}")
var Int16 = AXIOM("i16",Type); Int16.notation=blue("\\mathbb{i16}")
var Int32 = AXIOM("i32",Type); Int32.notation=blue("\\mathbb{i32}")
var Int64 = AXIOM("i64",Type); Int64.notation=blue("\\mathbb{i64}")

var BFloat16 = AXIOM("bf16",Type); BFloat16.notation=blue("\\mathbb{b16}")





//F=>SetField(Complex(F))

var oct=OctonionMk(Nat,1,2,3,4,5,6,7,8)





/*R.mk.notation = x=>{ //wrong this returns the function as a string!
    var s ="\\{";
    for(var i=0;i<5;i++){
        s+=x(i)+","
    }
    s+="...\\}";
    return s;
}*/


//--------------------PROPOSITIONS--------------------------


Prop.equals  = AXIOM("=", FORALL(Prop, G=>G.to(G.to(Prop)) ))
Prop.notequals  = AXIOM("pnotequals", FORALL(Prop, G=>G.to(G.to(Prop)) ))
var equals = Type.equals = AXIOM("=",FORALL(Type, G=>G.to(G.to(Prop)) )); 
var notequals = Type.notequals = AXIOM("notequals",FORALL(Type, G=>G.to(G.to(Prop)) )); 
//Nat.equals = equals(Nat)
Type1.equals = AXIOM("=", FORALL(Type1, G=>G.to(G.to(Prop)) ))
Type1.notequals = AXIOM("≠", FORALL(Type1, G=>G.to(G.to(Prop)) ))

equals.notation = Prop.equals.notation=Type1.equals.notation= type=>x=>y=> (fill(x) + "=" + ""+ y) 
notequals.notation = Prop.notequals.notation=Type1.notequals.notation= type=>x=>y=> (x + "≠" + ""+ y) 

//Prop.id = FUN(Prop,t=>FUN(t,x=>x))
//Type.id = FUN(Type,t=>FUN(t,x=>x))

Prop.id = defineVar(bold("id"), FUN(Prop,t=>FUN(t,x=>x)))
Type.id = defineVar(bold("id"), FUN(Type,t=>FUN(t,x=>x)))


var False = AXIOM("⊥",Prop);False.notation = red("⊥")
var True = AXIOM("⊤",Prop);True.notation = red("⊤")
True.proof = AXIOM("⊤.proof",True)

var lt = AXIOM("lt", FORALL(Type, G=>G.to(G.to(Prop)) ));     lt.notation=  type=>x=>y=> (x + "<" + ""+ y) 
var gt = AXIOM("gt",FORALL(Type, G=>G.to(G.to(Prop)) ));     gt.notation=  type=>x=>y=> (x + ">" + ""+ y)
var lte = AXIOM("lte", FORALL(Type, G=>G.to(G.to(Prop)) ));     lte.notation=  type=>x=>y=> (x + "≤" + ""+ y) 
var gte = AXIOM("gte", FORALL(Type, G=>G.to(G.to(Prop)) ));     gte.notation=  type=>x=>y=> (x + "≥" + ""+ y) 




//-------------FIELDS--------------
function SetField(A){
    A.plus = plus(A)
    A.sub = sub(A)
    A.times= times(A)
    A.divide= divide(A)
    A.power = power(A)
    A.equals = equals(A)
    A.notequals = notequals(A)

    //ordering or partial ordering
    A.lt = lt(A)
    A.gt = gt(A)
}
function SetOrderedField(A){

}
function isField(A){
    return A.plus!=undefined && A.sub!=undefined && A.times!=undefined && A.divide!=undefined && A.power!=undefined
}

   
SetField(Nat)
SetField(Rat)
SetField(Real)
SetField(Int)
SetField(PosRat)
//How to set fields such as Complex[Real]???





lt.prop =  AXIOM("ltprop",FORALL(Nat,a=>equals(Prop, Nat.lt(zero, succ(a) ) , True )))
gt.prop =  AXIOM("gtprop",FORALL(Nat,a=>equals(Prop, Nat.gt(succ(a),zero ) , True )))


//---------------------LIST----------------------
var List = AXIOM("L",Type.to(Type)) ;List.notation = type=>"{"+type+"}^{[*]}" //type=>blue("List")+"["+type+"]"
var LEnd = AXIOM("[]", FORALL(Type,F=>List(F))) ; LEnd.notation = type=>"\\{\\}";//"∅"
var LNext = AXIOM("Concat", FORALL(Type,T=>T.to(List(T).to(List(T))) ));
LNext.fastValue = t=>x=>rest=>{
    return rest.concat(x);
}
LEnd.fastValue = t=> [];

List.get= AXIOM("get",FORALL(Type, T=>Nat.to(List(T).to(T))))
List.get.notation = type=>n=>list=>list+"_{"+n+"}"
List.get.fastValue = type=>n=>list=>list[n];

List.Length = AXIOM("len",FORALL(Type, T=>List(T).to(Nat))); List.Length.fastValue = t=>L=>L.length;
List.Length.notation=t=>L=> "|"+L+"|";

var listLength1 = AXIOM("listlen1", 
    FORALL(Type, T=> FORALL( T, X=> FORALL( List(T), L=>
    equals(Nat,  List.Length(T , LNext(T, X , L))  , S( List.Length(T, L )  )       )
))))
var listLength0 = AXIOM("listlen0", 
    FORALL(Type, T=> FORALL( T, X=> FORALL( List(T), L=>
    equals(Nat,  List.Length(T , LEnd(T))  , Nat.zero       )
))))

List.Concat = AXIOM("concat",FORALL(Type, T=>List(T).to(List(T).to(List(T)) )));
List.Concat.fastValue = T=>L1=>L2=>L1.concat(L2);

List.Sum =  AXIOM("SumL", FORALL(Type, T=>List(T).to(T))); List.Sum.notation = T=>"\\sum"
List.Sum.fastValue = t=>l=>{
    var result=0;
    for(var i=0;i<l.length;i++) result+=l[i];
    return result;
}
//List.Sum(Nat,LIST(1,2,3,4))   
var listGet0 = AXIOM("listGet0", FORALL(Type, T=> FORALL(T,x0 => FORALL(List(T),rest=>equals(T,  List.get(T, zero, LNext(T , x0 , rest )   )  , x0    )))))
var listGet1 = AXIOM("listGet1", FORALL(Type, T=> FORALL(T,x0 => FORALL(Nat, n=> FORALL(List(T), rest=>equals(T,  List.get(T, succ(n), LNext(T, x0 , rest )   )  , List.get(T,n, rest  )  ))))))

var listLen =  AXIOM("listLen",FORALL(Type, T=>FORALL(T,element=>FORALL(List(T),L =>FORALL(Nat, n=> 
    equals(Nat, List.Length(T, LNext( T, element, L  )) , succ( List.Length( T,L) ) ) ) ) )))
var listLen0 =  AXIOM("listLen0",FORALL(Type, T=>FORALL(T,element=>FORALL(List(T),L =>FORALL(Nat, n=> 
    equals(Nat, List.Length(T, LEnd(T)) , Nat.zero   ) ) ) )))

var L= LNext(Nat,7,LNext(Nat,5,LNext(Nat,3, LEnd(Nat))))

LNext.openNotation = type=>x=>(rest,y)=>x+","+y.openNotation
LNext.notation = type=>x=>rest=>  "\\{"+x+","+rest+"\\}"
//LNext.notation = type=>(x,z)=>(rest,y)=> "\\left(" + x + "," + y.first.kind+"\\right)" 

function matchFunc(A,F,args){
    for(var i=0;i<args.length;i++){
        if(!F.first) return false;
        F=F.first;
    }
    return F.symbol==A.symbol
}

//better list notation  //A[A[A[LNext,Type],x],rest] 
LNext.notation = type=>x=>(rest,y)=>{
    //var result="\\{" + x;
    var result = x+"\\}";
    //matchFunc(y, LNext,(null,null,null))
    var i=0;
    while(y.kind=="applied" && y.first && y.first.first && y.first.first.first && y.first.first.first.symbol == LNext.symbol){
        //result+=","+y.first.second.toString();
        result = y.first.second.toString()+"," + result;
        y=y.second
        i++;
        if(i>20) {
            return "\\{..."+result;          
        }
    }
     if(y.kind=="applied" && y.first.symbol==LEnd.symbol) return "\\{"+result;// return result+ "\\}"
   // return result + y.toString() +"\\}"
    return "\\{"+y.toString() + result;
}


List.fromFunc = AXIOM("LfromF",FORALL(Type, T=>Nat.to(T).to(Nat.to(List(T)) )))  //List.fromFunc(Real, 3, FUN(Nat, x=>Real))

var listFromFunc1 =   FORALL(Type, T=>FORALL(Nat, N=>FORALL(Nat.to(T),F=>equals(List(T),  List.fromFunc(T, F,succ(N)  ),   LNext(T, F(N) ,  List.fromFunc(T,F,N)  ) ) )))
var listFromFunc0 =   FORALL(Type, T=>FORALL(Nat.to(T),F=>equals( List(T),  List.fromFunc(T, F,Nat.zero  ),   LEnd(T ) ) ))
List.fromFunc.fastValue = t=>f=>n=>{
    var result=[];
    for(var i=0;i<=n;i++){
        result.push( f(i) )
    }
    return result;
}

//---------------GROUP THEORY-----------------------------

var Permutation = NewType("Permutation")
Permutation.mk = AXIOM("Permutation.mk" , List(Nat).to(Permutation))
Permutation.times = AXIOM("Ptimes", Permutation.to(Permutation.to(Permutation)))

//var mylist = LNext(Nat,3,LNext(Nat,5,LEnd(Nat)))



//---sum-------------
var sum= AXIOM("sum", FORALL(Type, T=>Nat.to(T).to(Nat.to(T))) ) //sum(F, a) = f(0)+f(1)+f(2)+...f(a)
sum.notation = type=>(F,y)=>n=>{
    if(y && y.kind=="fun"){
        var vari=new C(getNewVariName(),y.vari.type)
        return "\\sum\\limits_{"+vari+"=0}^{"+n+"} \\left\\{" + fill(y.appliedTo(vari).toString()) +"\\right\\}" 
    }else
    return "\\sum\\limits_{0}^{"+n+"}"+F
}
sum.fastValue = t=>f=>n=>{
    var result=0;
    for(var i=0;i<=n;i++){
        result+= f(i)
    }
    return result;
}

//sum.notation = type=>F=>n=>"\\sum\\limits_{"+F.vari+"=0}^{"+n+"}"+F.second //F is a string! (same problem again!)

var sumProp =  AXIOM("sumProp", FORALL(Type, T=>FORALL(Nat.to(T), F=>FORALL(Nat,n=>
    equals( T , sum(T, F , succ(n) ) , plus(T, F(succ(n)) , sum(T, F , n )   )    )
 )    )  )   )

 var sumProp0 =  AXIOM("sumProp0", FORALL(Type, T=>FORALL(Nat.to(T), F=>
    equals( T , sum(T, F , zero ) , APPLY(F,zero) ) )))




//--product-----
var prod= AXIOM("prod", FORALL(Type, T=>Nat.to(T).to(Nat.to(T))) ) //prod(F, a) = f(0)*f(1)*f(2)*...f(a)
prod.notation = type=>(F,y)=>n=>{
    if(y && y.kind=="fun"){
        var vari=new C(getNewVariName(),y.vari.type)
        return "\\prod\\limits_{"+vari+"=0}^{"+n+"} \\left\\{" + y.appliedTo(vari) +"\\right\\}" 
    }else
    return "\\prod\\limits_{0}^{"+n+"}"+F
}
prod.fastValue = t=>f=>n=>{
    var result=1;
    for(var i=1;i<=n;i++){
        result*= f(i)
    }
    return result;
}


var prodProp =  AXIOM("prodProp", FORALL(Type, T=>FORALL(Nat.to(T), F=>FORALL(Nat,n=>
    equals( T , prod(T, F , succ(n) ) , times(T, F(succ(n)) , prod(T, F , n )   )    )
 )    )  )   )

 var prodProp0 =  AXIOM("prodProp0", FORALL(Type, T=>FORALL(Nat.to(T), F=>
    equals( T , prod(T, F , zero ) , APPLY(F,1) ) )))

var limit =  AXIOM("limit", Nat.to(Real).to(Type))


//---------iterator
var iter= AXIOM("iter", FORALL(Type, T=>(T.to(T)).to(T.to(Nat.to(T))) )) //iter(F,x,n) = f(f(f(f(x))))
iter.notation = type=>F=>x=>n=>"\\left("+F+"\\right)^{"+n+"}("+x+")"

iter.fastValue = t=>f=>x=>n=>{
    var result=x;
    for(var i=0;i<n;i++){
        result=f(result)//.float();
    }
    return result;
}

var iterProp =  AXIOM("iterProp", FORALL(Type, T=>FORALL(T.to(T), F=>FORALL(Nat,n=> FORALL(T, x=>
    equals( T , iter(T, F , x, succ(n) ) , F( iter(T, F,x,  n ) )  )    )
 )    )  )   )

 var iterProp0 =  AXIOM("iterProp0", FORALL(Type, T=>FORALL(T.to(T), F=>FORALL(T, x=>
    equals( T , iter(T, F , x,  zero ) , x ) ))))



/*   Can we do this automatically:
====================================
//prop =       FORALL(?,  A=>   FORALL(?,  B=>   FORALL( ?,   C=>  equals( Dot(A)(B)(C).. , Dot.Def(A)(B)(C)...  )
*/



var makeList = AXIOM("MakeList", FORALL(Type, F=>(Nat.to(F)).to(Nat.to(List(F)))   ))
var makeListP = AXIOM("MakeListP", FORALL(Type, T=>FORALL( Nat.to(T), F=>  FORALL(Nat, n=> 
         equals(List(T) ,  makeList(T,F,succ(n)) ,  LNext( T, F(succ(n)),  makeList(T,F,n)  )  )))))
var makeList0 = AXIOM("MakeList0", FORALL(Type, T=>FORALL( Nat.to(T), F=> 
            equals(List(T) ,  makeList(T,F,zero) ,  LEnd(T)  )  )))

// ----------------REALS--------------------
/*
var Pi = AXIOM("\\pi", Real)
Pi.def = R.mk( FUN(Nat, n=> sum(Rational,FUN(Nat, k=>RationalMk(8,Nat.times(Nat.plus(Nat.times(4,k),1),Nat.plus(Nat.times(4,k),3))) )  ,n   )  ))
Pi.prop = AXIOM("PiDef", equals(Real, Pi, PiSeries))
*/
/*var Pi = defineVar("pi",
    R.mk( FUN(Nat, n=> sum(Rational,FUN(Nat, k=>Rat.mk(8,Int.times(Int.plus(Int.times(4,Int.mk(k,0)),1),Int.plus(Int.times(4,Int.mk(k,0)),3))) )  ,n   )  ))
    ,"\\pi"
)*/
var Pi = defineVar("pi",
    R.mk( FUN(Nat, n=>  sum(Rational,FUN(Nat, k=>Rat.mk(Int.times(4,Int.power(-1,k)),Int.plus(Int.times(2,Int.mk(k,0)),1)) )  ,n   )    ))
    ,"\\pi"
)
var Pi2 = defineVar("pi2",
    R.mk( FUN(Nat, n=> 
        Rational.sub(
        sum(Rational,FUN(Nat, k=>Rat.mk(Int.times(4,Int.power(-1,k)),Int.plus(Int.times(2,Int.mk(k,0)),1)) )  ,n   ) 
        , Rational.mk(1,Int.mk(n,0))
        )
    ))
    ,"\\pi"
)

Pi.fastValue = Math.PI;
/*
var PiTest = defineVar("piTest",
    R.mk( FUN(Nat, n=>sum(Rational,FUN(Nat, k=>Rat.mk(Int.mk(k,0),1 ))  ,n   )  ))
    ,"piTest"
)*/

Real.fromRat = AXIOM("castReal",Rat.to(Real))  ;   Real.fromRat.fastValue = x=>x;
Real.fromRat.notation = x=> "("+x+")"+subscript(blue("ℝ"))
Real.fromRat.def = FUN(Rational,x=>R.mk( FUN(Nat,_=>x )  ))
Real.fromRat.prop = FORALL(Rational, x=> equals(Real, Real.fromRat(x) , Real.fromRat.def(x)  ))

var RealRatPlus = AXIOM("realRatPlus", FORALL(Rational, x=>FORALL(Rational, y=>equals(Real,  
    Real.plus( Real.fromRat(x), Real.fromRat(y) )  , 
    Real.fromRat(Rat.plus(x,y))
) )))

var RealRatTimes= AXIOM("realRatPlus", FORALL(Rational, x=>FORALL(Rational, y=>equals(Real,  
    Real.times( Real.fromRat(x), Real.fromRat(y) )  , 
    Real.fromRat(Rat.times(x,y))
) )))

/*
Real.zero = defineVar("0","0_{ℝ}",Real,
    R.mk( FUN(Nat, n=> Rat.zero)  )
)
Real.one = defineVar("0","0_{ℝ}",Real,
    R.mk( FUN(Nat, n=> Rat.one)  )
)*/
Real.zero = Real.fromRat(Rat.zero)
Real.one = Real.fromRat(Rat.one)

var Zmod =  AXIOM("zmod",Nat.to(Type)); Zmod.notation = n=>blue("\\mathbb{Z}")+"_{"+n+"}" ; Zmod.fastValue=n=>null;

Zmod.fromNat =  AXIOM("fromNat",FORALL(Nat, n=>Nat.to(Zmod(n)))); 
Zmod.fromNat.notation = n=>x=>{
    return "("+x+")_{"+blue("\\mathbb{Z}")+"_{"+n+"}}"
}
Zmod.fromNat.fastValue = x=>y=>y%x

Zmod.toNat =  AXIOM("toNat",FORALL(Nat, dim=>Zmod(dim).to(Nat))); 

var factorial = AXIOM("!", Nat.to(Nat))
factorial.postfix= true
var factRuleN = FUN(Nat ,  x=> new Rule( factorial( succ(x)  ) , Nat.times( succ(x), factorial(x)  )     )     )
var factRule0 = FUN(Nat ,  x=> new Rule( factorial( zero ) , one )     )  
factorial.fastValue = n=>{
    var result=1;
    for(var i=1;i<=n;i++){
        result*=i;
    }
    return result;
}


var E = defineVar("e",R.mk( FUN(Nat, j=>sum(Rat,FUN(Nat, n=> Rat.mk( Int.one, Int.mk(factorial(n),0) ) ),  j) )))

//var E = defineVar("e",R.mk( FUN(Nat, n=> Rat.mk( Int.power( Int.plus(Int.mk(n,0),1),n ), Int.power(Int.mk(n,0),n)    ) ) ) , "e")
E.fastValue = Math.exp(1.0);




var Sqrt2 = R.mk( FUN(Nat, n=> iter(Rat,FUN(Rat, x=> Rat.plus(Rat.divide(1,x) , Rat.divide(x,2 )    )  )  , 1, n ) ) )
Sqrt2.fastValue=Math.sqrt(2.0)

var R2R = R.to(R);

var z = AXIOM("z",Real)
var w = AXIOM("w",Real)
var Sin = AXIOM("sin", Real.to(Real)); Sin.notation = "\\sin";            Sin.fastValue= Math.sin
var Cos = AXIOM("cos", Real.to(Real)); Cos.notation = "\\cos";            Cos.fastValue= Math.cos
var Tan = AXIOM("tan", Real.to(Real)); Tan.notation = "\\tan";            Tan.fastValue= Math.tan    
var Exp = AXIOM("exp", Real.to(Real)); Exp.notation = x=>"e^{"+x+"}";     Exp.fastValue= Math.exp
var Log = AXIOM("log", Real.to(Real)); Log.notation = "\\ln";          Log.fastValue= Math.log

var Erf = AXIOM("erf",R2R); Erf.fastValue = x=>myerf(x);
var Gamma = AXIOM("\\Gamma",R2R); Gamma.fastValue = x=>mygamma(x);


R.sin=Sin
R.cos=Cos



R2R.fromReal = AXIOM("castR2R",Real.to(R2R))
R2R.fromReal.notation = x=> "("+x+")"+subscript(blue("ℝ\\rightarrow ℝ"))
R2R.fromReal.def = FUN(R,x=> FUN(R,_=>x ) )
R2R.fromReal.prop = FORALL(Real, x=> equals(R2R, R2R.fromReal(x) , R2R.fromReal.def(x)  ))

//Trig identities

var sinPiZero = AXIOM("sinPiZero",Real.equals( Sin(Pi), Real.zero))
var sinZero   = AXIOM("sinZero",  Real.equals( Sin(Real.zero), Real.zero))
var cosZero   = AXIOM("cosZero",  Real.equals( Cos(Real.zero), Real.one))

var sinSum = AXIOM("sinSum",FORALL(R,x=>FORALL(R,y=>
    R.equals( R.sin(R.plus(x,y)), R.plus(R.times(R.sin(x),R.cos(y)), R.times(R.cos(x),R.sin(y))  )))))
var cosSum = AXIOM("cosSum",FORALL(R,x=>FORALL(R,y=>
    R.equals( R.cos(R.plus(x,y)), R.sub(R.times(R.cos(x),R.cos(y)), R.times(R.sin(x),R.sin(y))  )))))

var toCauchy = AXIOM("cauchy",Real.to(Nat.to(Rational)) ) //gets the cauchy series for the reals
toCauchy.notation=  r=>n=>(red("\\mathcal{C}")+subscript(n)+""+r);

toCauchy.fastValue = (x,y)=>n=>{
    
    if(y.kind=="applied" && y.first.symbol==R.mk.symbol &&  y.second.kind=="fun"){
        console.log("YES")
        return y.second.float(0)(n)
    }
}

var realSeriesProp = sorry(FORALL(Nat.to(Rational), F=> equals(Nat.to(Rational)  ,toCauchy( R.mk(F)   )   , F  )   ))

Real.Add = FUN(Real, x=>FUN(Real, y=>   R.mk( FUN(Nat,n=> plus(Rational, toCauchy(x)(n) ,  toCauchy(y)(n)  ) )   )))
Real.Exp = defineVar("Real.Exp",FUN( Real, x=> R.mk(FUN(Nat, n=> divide(Rational, power(Rational, plus(Rational, RationalMk(IntMk(n,0),1),  toCauchy(x)(n)    ),n ), RationalMk( IntMk(Nat.power(n,n),0) ,1)   ) ))    ))
Real.Exp.notation = x=>"e^{"+x+"}"
Real.Exp.fastValue = x=>Math.exp(x)
Real.Sqrt = AXIOM("real.sqrt", Real.to(Real)); Real.Sqrt.notation = x=>"\\sqrt{"+x+"}"; Real.Sqrt.fastValue = Math.sqrt

sqrtTimes = AXIOM("sqrtTimes" , FORALL(Real,x=>FORALL(Real,y=>equals(Real, Real.times(Real.Sqrt(x),Real.Sqrt(y)) ,Real.Sqrt(Real.times(x,y)) ))))
sqrtSquare = AXIOM("sqrtSquare" , FORALL(Real,y=>equals(Real, Real.times(Real.Sqrt(y),Real.Sqrt(y)) ,y )))

var realAddProp =  AXIOM("realAddProp", FORALL(Real, x=>FORALL(Real, y=> equals(Real, plus(Real, x,y) ,
    R.mk(  FUN(Nat, n=> plus(Rational,  toCauchy(x)(n) , toCauchy(y)(n) ) )
    )))))
var realSubProp =  AXIOM("realSubProp", FORALL(Real, x=>FORALL(Real, y=> equals(Real, sub(Real, x,y) ,
    R.mk(  FUN(Nat, n=> sub(Rational,  toCauchy(x)(n) , toCauchy(y)(n) ) )
    )))))
var realMulProp =  AXIOM("realMulProp", FORALL(Real, x=>FORALL(Real, y=> equals(Real, times(Real, x,y) ,
    R.mk(  FUN(Nat, n=> times(Rational,  toCauchy(x)(n) , toCauchy(y)(n) ) )
    )))))

//var BigInt = AXIOM("BigInt",Type)
//BitInt.toNat = AXIOM("BitIntToNat" ,Nat.to(BigInt) )

var compose = AXIOM("compose", R2R.to(R2R.to(R2R)))
compose.notation = x=>y=>"("+fill(x)+"∘"+fill(y)+")"
var composeFunc = AXIOM("composeFunc", FORALL(R2R, F=>FORALL(R2R, G=> equals(R2R,  FUN(Real, x=>F(G(x))), compose(F,G) ))))
var composeFunc2 = AXIOM("composeFunc", FORALL(R2R, F=>FORALL(R2R, G=> FORALL(Real, x=>equals(Real,  F(G(x)) , compose(F,G)(x) ))))) //too powerful!

var Compose = AXIOM("Compose",FORALL(Type, T=> ( T.to(T) ).to(( T.to(T) ).to( T.to(T) ))))
Compose.notation = t=>x=>y=>"("+fill(x)+"∘"+fill(y)+")"; Compose.fastValue = t=>f=>g=>(x=>f(g(x)))
var Comp3 = AXIOM("Comp3",FORALL(Type, T=>FORALL(Type,U=>FORALL(Type, V=>( T.to(U) ).to(( U.to(V) ).to( T.to(V) )))))); 
Comp3.notation = t=>u=>v=>x=>y=>"("+fill(x)+"∘"+fill(y)+")"

//------------------real calculus------------
//x=>[f(x+1/n)-f(x)] / (1/n)

var deriv = FUN(Real.to(Real), F=>FUN(Real, x=> R.mk( FUN(Nat, n=>
        Rat.divide( 
            Rat.sub( 
                toCauchy( F( R.mk( FUN(Nat, m=>Rat.plus( toCauchy(x)(m), RationalMk(1,Int.mk(n,0)) ) ) )))(n) , 
                toCauchy( F(x) )(n)  
            ),  
         RationalMk(1,Int.mk(n,0)) )
    ))))

var deriv2 = FUN(Real.to(Real), F=>FUN(Real, x=> 
    Real.times( Real.sub( F( Real.plus( x , R.mk(FUN(Nat,n=>RationalMk(Int.one,Int.mk(n,0))  )) )  ), F(x) ), R.mk(FUN(Nat,n=>RationalMk(Int.mk(n,0),1)))
)))

var integrate2 = FUN(Real.to(Real), F=>FUN(Real, x=> 
    Real.mk( FUN(Nat,n=>
    toCauchy(Real.times(sum( Real, FUN(Nat, i=>  F( Real.times(x , Real.fromRat(Rat.mk(Int.mk(i,0),Int.mk(n,0)) )  )     ) ),n) , Real.divide(x , Real.fromRat(Rat.mk(Int.mk(n,0),1))) ))
        (n)
))))

//This one works better we call toCauchy on x and on F(x) and do rest with rationals
var integrate = FUN(Real.to(Real), F=>FUN(Real, x=> 
    Real.mk( FUN(Nat,n=>Rat.times(sum( Rat, FUN(Nat, i=>toCauchy( F( Real.mk( FUN(Nat, m=>  Rat.times(toCauchy(x)(m), Rat.mk(Int.mk(i,0),Int.mk(n,0)) ) )  )  ) )(n)),n) , Rat.divide( toCauchy(x)(n) , Rat.mk(Int.mk(n,0),1)) )    
))))

//toCauchy(integrate(Type.id(Real))(Real.fromRat.def(1)))(10)
//toCauchy(integrate(FUN(Real, z=>Real.times(z,z)))(Real.fromRat.def(10)))(30)

//integral 0...x
//x=> sum( f(x*i/n) *(x/n)  ,i = 0...n ) 
var Integral = AXIOM("Integral", Real.to(Real).to(Real.to(Real)))
Integral.notation = (x,y)=>z=>
    {
        if (y && y.kind=="fun"){
            
            var vari=new C(getNewVariName(),y.first)
            return "\\int\\limits_0^{"+z+"}\\left("+y.appliedTo(vari)+"\\right) d"+vari+"" 
        }else{
            return "\\int " + fill(x)
        }
    }

var Deriv = defineVar("Deriv", deriv);

//var Deriv = AXIOM("Deriv", R2R.to(R2R))
Deriv.notation = (x,y)=>z=>
    {

        if (y && y.kind=="fun"){
            var vari=new C(getNewVariName(),y.first)
            return "\\frac{\\partial "+fill(y.appliedTo(vari).toString())+"}{\\partial "+vari+"}|_{"+vari+"="+fill(z.toString())+"}" 
        }else{
            var v = getNewVariName() 
            return "D\\left["+fill(x)+"\\right]"
            //return "\\frac{\\partial}{\\partial "+v+"}"+fill(x)+"("+v+")|_{"+v+"="+z+"}" 
            //return "\\frac{\\partial "+fill(x)+"("+v+")}{\\partial "+v+"}|_{"+v+"="+z+"}" 
            //return "\\partial" + x;
        }
    }

var DerivT = AXIOM("DerivT",FORALL(Type, T=>Real.to(T).to(Real.to(T))))
DerivT.notation = t=>(x,y)=>z=>
{
    if (y && y.kind=="fun"){
        var vari=new C(getNewVariName(),y.first)
        return "\\frac{\\partial "+fill(y.appliedTo(vari).toString())+"}{\\partial "+vari+"}|_{"+vari+"="+fill(z.toString())+"}" 
    }else{
        var v = getNewVariName() 
        return "D\\left["+fill(x)+"\\right]"
    }
}


var combineDerivSum = AXIOM("DerivSum",
    FORALL(R2R, F=>FORALL( R2R ,G=> FORALL(Real, x=>
        equals( Real,  
            Real.plus( Deriv(F,x), Deriv(G,x)  ),
            Deriv(FUN(Real,y=>plus(Real,F(y),G(y))),x)
        )
))))

var Id = AXIOM("id",R2R); Id.notation="\\mathbf{id}" //=FUN(R,x=>x)
//var derivSin = AXIOM("DerivSin",  FORALL(Real, x=>   equals( Real,   Deriv(Sin,x),   Cos(x)  )))
var derivSin2 = AXIOM("DerivSin",   equals( R2R,   Deriv(Sin),   Cos  ))
var derivCos2 = AXIOM("DerivCos",   equals( R2R,   Deriv(Cos),  times(R2R, -1, Sin ) ))
var intCos2 = AXIOM("IntCos",   equals( R2R,   Integral(Cos),   Sin  ))
var intSin2 = AXIOM("IntSin",   equals( R2R,   Integral(Sin),  times(R2R, -1, Cos)  ))
var derivSqrt = AXIOM("DerivSqrt",   equals( R2R,   Deriv(Real.Sqrt),   divide(R2R,-0.5,Real.Sqrt)  ))


//NOT TRUE if F or G depends on x!
var derivCompos = AXIOM("DerivCompos", FORALL(R2R, F=>FORALL(R2R, G=>equals( R2R, Deriv(compose(F,G)), times(R2R,compose( Deriv(F),G ),Deriv(G) )   ) )))

var derivPlus = AXIOM("DerivPlus",  FORALL(R2R, F=>FORALL(R2R, G=>equals( R2R, Deriv(plus(R2R,F,G)),  plus(R2R, Deriv(F)  ,Deriv(G) )   ) )))
var derivTimes = AXIOM("DerivTimes",  FORALL(R2R, F=>FORALL(R2R, G=>equals( R2R, Deriv(times(R2R,F,G)),  plus(R2R, times(R2R,Deriv(F),G)  ,times(R2R,F, Deriv(G) )   ) ))))

//Deriv(FUN(Real,x=>Sin(x))) ---------> Deriv(Sin)????        (F=FUN(Real,vari="_x",second=Sin("_x")))
var simpFunc = AXIOM("simpFunc",  FORALL(R2R, F=> equals(R2R,  FUN(Real, x=> F(x) )  , F ) ) ) //should this work?

var derivConst = AXIOM("DervConst" ,  FORALL(Real, x => equals( R2R, Deriv( R2R.fromReal( x ) ) , R2R.fromReal (Real.zero) ) ) )
var derivId =    AXIOM("DervId" ,     FORALL(Real, x => equals( R2R, Deriv( Id ) , R2R.fromReal (Real.one) ) ) )


var integral = FUN(Real.to(Real), F=>FUN(Real, x=> R.mk( FUN(Nat, n=>
    Rat.times( 
        sum(Rational,
            FUN(Nat, i=> Rat.times
              ( 
                toCauchy(x)(n),
                toCauchy(    F(  R.mk(  FUN( Nat, m=> Rat.times ( toCauchy(x)(m) , RatMk(Int.mk(i,0),Int.mk(n,0)) )  ))  )    )(n)       
              )  
            )  
        ,n),  
     RationalMk(1,Int.mk(n,0)) ) ///* x
))))

//---------------Calculus of Variations (equivalent to continuous partial derivatives)


var R2R2R2R = R2R.to(R2R)

var Vari = AXIOM(x=>"\\delta", R2R2R2R)


//Here power means multiplicative power 
// delta( Id^n ) =  n*Id^(n-1) 
// delta( D^n ) =  -n*(DoD) D^(n-2) = -n* D o (D^(n-1)  ) ? 
// delta( Id^n D^m ) = 
// delta( A x B) = delta(A) x B + A x delta(B) ??
// delta( A o B) = 
// delta( D o B) =


//-------------------------------------------------PARTIAL DERIVAVITES

var VectorSpace = AXIOM("V",Type)
//var Euc = AXIOM("Euc",Nat.to(VectorSpace)  ); Euc.notation = n=>blue("\\mathbb{E}")+"^{"+n+"}"
//var Euc = FUN(Nat, n=> Zmod(n).to(R))
var Vect = FUN(Nat,n=>FUN(Type, T=> Zmod(n).to(T)))
//var Euc = FUN(Nat,n=>Zmod(n).to(R))
var GL = FUN(Nat,n=>FUN(Type, T=> Zmod(n).to(Zmod(n).to(T) )))


//var GLR = GL(R)
//Euc = Vec(R)
//var U = AXIOM("U",Euc(3)) ; U.notation = n=>"U_{"+n+"}"
//var V = AXIOM("V",Euc(3)) ; V.notation = n=>"V_{"+n+"}"




var FF=dim=>Euc(dim).to(R)

var Vector = AXIOM("Vector", Type.to(Nat.to(Type))) ;Vector.notation = (T,y)=>n=>{
    if(y.kind!="atom") return "{("+ T+")}^{"+n+"}"
    return "{"+ T+"}^{"+n+"}"
}
var Vec=Vector;
Vector.start = AXIOM("start",FORALL(Type, T=>Vector(T)(0))) ; Vector.start.notation= T=>"\\ "//_{"+T+"}"
Vector.mk = AXIOM("Vec.mk", FORALL(Type, T=>FORALL(Nat, n=>T.to( Vector(T)(n)   .to(Vector(T)(succ(n)))  )  )))
Vector.mk.notation = T=>(n,m)=>x=>rest=>"\\left["+rest+"," + x+"\\right]"//_{{"+T+"}^{"+succ(m)+"}}"
Vector.start.fastValue = T=>[];
Vector.mk.fastValue = T=>n=>x=>rest => rest.concat(x);

var Proj = AXIOM("Proj",Type.to(Nat.to(Type))); Proj.notation = t=>n=> t +blue("\\mathbb{P}")+"^{"+n+"}";

Proj.get = AXIOM("ProjGet" ,FORALL(Type, T=>FORALL(Nat, dim=> Proj(T,dim).to(Zmod(dim).to(T))) ));
Proj.get.notation = t=>dim=>vect=>index =>"{"+vect+"}"+subscript(index);


var Iso = AXIOM("Iso", Type.to(Type.to(Prop))); Iso.notation = a=>b=>a+"\\cong "+b;

var Euc = FUN(Nat,dim=>Vector(Real)(dim) )
//var Euc=dim=>Vector(Real)(dim)

var U=AXIOM("U",Vector(Real)(3))
var V=AXIOM("V",Vector(Real)(3))

//dual vectors (needed?)
var VectorT = AXIOM("Vector", Type.to(Nat.to(Type))) ;VectorT.notation = T=>n=>"{"+ T+"}_{"+n+"}"
var VecT=VectorT;
VectorT.start = AXIOM("start",FORALL(Type, T=>VectorT(T)(0))) ; VectorT.start.notation= T=>"\\ "//_{"+T+"}"
VectorT.mk = AXIOM("Vec.mk", FORALL(Type, T=>FORALL(Nat, n=>T.to( VectorT(T)(n)  .to(VectorT(T)(succ(n)))  )  )))
VectorT.mk.notation = T=>(n,m)=>x=>(rest,y)=>{
    //should check if rest==start
    return "\\begin{bmatrix}{"+rest+"}\\\\{"+x+"}\\end{bmatrix}"
}
VectorT.start.fastValue = T=>[];
VectorT.mk.fastValue = T=>n=>x=>rest => rest.concat(x);

Vector.get = AXIOM("Vget" ,FORALL(Type, T=>FORALL(Nat, dim=> Vector(T,dim).to(Zmod(dim).to(T))) ));
Vector.get.notation = t=>dim=>vect=>index =>"{"+vect+"}"+subscript(index);



var Dot = AXIOM("dot",FORALL(Nat,dim=>Euc(dim).to(Euc(dim).to(R)) ) ); 
Dot.def = FUN(Nat, dim=> FUN(Euc(dim), X=>FUN(Euc(dim),Y=>sum(R , FUN(Nat, n=> times( R  , 
    Vector.get(Real,dim,X,Zmod.fromNat(dim,n) ) , Vector.get(Real,dim,Y, Zmod.fromNat(dim,n)  )  )  ) ,dim   ))))
//Dot.def = FUN(Nat, dim=> FUN(Vector(Real)(dim), X=>FUN(Vector(Real)(dim),Y=>sum(R , FUN(Nat, n=> times( R  , X(Zmod.fromNat(dim,n) ) , Y( Zmod.fromNat(dim,n)  )  )  ) ,dim   ))))

Dot.prop = FORALL(Nat,dim=>FORALL(Euc(dim),X=> FORALL(Euc(dim), Y=> equals( R,   Dot(dim)(X,Y), Dot.def(dim)(X,Y)  ) )))
Dot.notation = dim=>X=>Y=>"("+fill(X)+"·"+fill(Y)+")"

var DotT = AXIOM("dot",FORALL(Type, T=>FORALL(Nat,dim=>(Zmod(dim).to(T)).to((Zmod(dim).to(T)).to(T)) ) )); 
//DotT.notation = type=>dim=>X=>Y=>"("+fill(X)+"·"+fill(Y)+")"
DotT.notation = type=>dim=>X=>Y=>{
    var index=getNewVariName()
    return "("+fill(X(index))+"·"+fill(Y(index))+")"
}
    

var TraceT = AXIOM("trace",FORALL(Type, T=>FORALL(Nat,dim=>(Zmod(dim).to(Zmod(dim).to(T))).to(T)) ) ); 
//DotT.notation = type=>dim=>X=>Y=>"("+fill(X)+"·"+fill(Y)+")"
TraceT.notation = type=>dim=>X=>{
    var index=getNewVariName()
    //return "["+fill(X)+"]"
    if( typeof X == 'function') X=X(index)
    if( typeof X== 'function') X=X(index)
    return "["+fill(X)+"]"
}
//Dot.notation = dim=>X=>Y=>"(\\delta^{\\mu\\nu}"+fill(X("\\mu"))+""+fill(Y("\\nu"))+")"


var MatMul =  AXIOM("matmul",FORALL(Type,T=>FORALL(Nat,dim=>GL(dim)(T).to(GL(dim)(T).to(GL(dim)(T))) ) ));  MatMul.notation =T=> dim=>X=>Y=>"("+fill(X)+"·"+fill(Y)+")"
MatMul.def = FUN(Type, T=>FUN(Nat, dim=> FUN(GL(dim)(T), X=>FUN(GL(dim)(T),Y=>
    FUN(Zmod(dim),i=> FUN(Zmod(dim), k=>
    sum(T , FUN(Nat, j=> times( T,  X(i)(Zmod.fromNat(dim,j)) , Y(Zmod.fromNat(dim,j))(k)   )  ) ,dim   ))))  )))

var B= AXIOM("B",GL(3)(R))


//symbolic deriv d/dx

//Dummy variables???
var SDeriv = AXIOM("SDeriv" , Real.to(Real));
SDeriv.notation = x=>fx=>"\\frac{d "+fx+"}{"+x+"}";


//var SDeriv


//In ForAlls and functions can the type be deduced???

//var Euc = n=>Zmod(n).to(R)

var phi = AXIOM("\\phi", Euc(3).to(Real))
//Functional Identity
//ID(dim)(n)  A_n(x)-->B_n(x)
var VID = AXIOM("VID",FORALL(Nat, n=>Nat.to(( Euc(n).to(Real)  ).to( Euc(n).to(Real)    )  ) )); VID.notation = dim=>i=>"ID_{"+i+"}"
var ID = AXIOM("ID",FORALL(Nat, n=>( Euc(n).to(Real)  ).to( Euc(n).to(Real)    )   )); ID.notation = dim=>"ID"

//PDeriv(3)(2) = d/dx_2 f( x )
var PDeriv = AXIOM("PDeriv", FORALL(Type, T=>FORALL(Nat, n=>Zmod(n).to(Euc(n).to(T).to(Euc(n).to(T))))))
PDeriv.notation = t=>dim=>i=>(f,y)=>
    {

        if (y && y.kind=="fun"){
            return (x,y)=>z=>"\\frac{\\partial "+fill(y.second)+"}{\\partial "+y.vari+"}|_{"+y.vari+"="+z+"}"
        }else{
            var v = getNewVariName() 
            return "\\partial_{"+i+"}" + f;////\\left["+fill(x)+"\\right]" //z=?
            //return "\\frac{\\partial}{\\partial "+v+"}"+fill(x)+"("+v+")|_{"+v+"="+z+"}" 
            //return "\\frac{\\partial "+fill(x)+"("+v+")}{\\partial "+v+"}|_{"+v+"="+z+"}" 
            //return "\\partial" + x;
        }
    }

var VDeriv = AXIOM("VDeriv", FORALL(Nat, dim=>Vector( Euc(dim).to(Real) , dim )  ))

var E3=Euc(3)
E3.PDeriv = PDeriv(Real,3)
//sum(Deriv(Sin(x)+Cos(x))) = Deriv(Sin(x))+Deriv(Cos(x))
/*var Div =  FUN(Nat, dim=> sum(FF(dim).to(FF(dim)) ,FUN(Nat, i=>Compose( FF(dim), PDeriv(dim,i) , ID(dim)  ))  , dim   ) ) 
var Laplacian = FUN(Nat, dim=> sum(FF(dim).to(FF(dim)) ,FUN(Nat, i=>
  Compose( FF(dim), PDeriv(dim,i), Compose( FF(dim), PDeriv(dim,i) , ID(dim)  ) )
)  , dim   ) ) */
var Div =  FUN(Nat, dim=> sum(FF(dim).to(FF(dim)) ,FUN(Nat, i=>PDeriv(Real,dim,Zmod.fromNat(dim,i)))  , dim   ) )  //WRONG! should be d.u 
var Laplacian = FUN(Nat, dim=> sum(FF(dim).to(FF(dim)) ,FUN(Nat, i=>
  Compose( FF(dim), PDeriv(Real,dim,Zmod.fromNat(dim,i)), PDeriv(Real,dim,Zmod.fromNat(dim,i)) )
)  , dim   ) ) 

 LaplacianT = defineVar("Laplacian", FUN(Type, T=>FUN(Nat, dim=> sum(( Euc(dim).to(T)   ).to( Euc(dim).to(T)    ) ,FUN(Nat, i=>
    Compose( Euc(dim).to(T) , PDeriv(T,dim,Zmod.fromNat(dim,i)), PDeriv(T,dim,Zmod.fromNat(dim,i)) )
  )  , dim   ) ) ) )
  LaplacianT.notation = t=>dim=>"\\nabla^2"

  //GradT ( F_n(x_3) )
//var GradT = AXIOM("Grad" , FORALL(Type, T=>FORALL(Nat, dim=>   (Euc(dim).to(T) ).to( Vector( Euc(dim).to(T)    )(dim)   )     )));
var GradT = AXIOM("Grad" , FORALL(Type, T=>FORALL(Nat, dim=>   (Euc(dim).to(T) ).to( Euc(dim).to( Vector(T   )(dim)   )     ))));
GradT.notation = t=>dim=>"\\nabla";

//Laplacian = FUN(Nat, dim=>  PDeriv(dim,Zmod.fromNat(dim,2))  )  //gives typeof=object!
//FF=dim=>Euc(dim).to(R) //<---probably a bad idea!
//var Grad-->E^n
//var Curl-->E^3

//-------------------------------TENSORS---------------------------------
var Tensor = AXIOM("Tensor",Type.to(Nat.to(Nat.to(Type)))  ) //Tensor(3,dim,Real) M_{abc}
Tensor.notation = T=>dim=>num_indices=>{
    //return "{"+T+"}^{{"+dim+"}^{"+num_indices+"}}"
    return "({"+T+"}^{"+dim+"})^{\\otimes "+num_indices+"}"
    //return "{"+T+"}^{"+ new Array(Number(num_indices)).fill(dim).join("\\times")  +"}"
}
Tensor.get = AXIOM("Tensor.get",FORALL(Type,T=>FORALL(Nat,dim=>FORALL(Nat, rank=>Tensor(T,dim,rank).to( List( Zmod(dim) ).to(T)  )    ))  ) );
Tensor.get.notation = T=>dim=>rank=>A=>L=>{
    return "{"+A+"}"+subscript(L);
}

//Tensor.get(    )  //Tensor.get(Real, 3,2,tensor(Real,3,2),[mu,nu,tau])// List of indices?
//var TensorProductType = = AXIOM("TensorPT",   )


var funnyTwo= AXIOM("funnyTwo", two )

//var forAll2E1P1 = new ForAll("x",Nat,twoEqualsOnePlusOne)
var forAllxEqx = new ForAll(new C("x'", Nat), x => equals(Nat,x,x) )
var forAllyEqy = new ForAll(new C("y'", Nat), x => equals(Nat,x,x) )
//var existsxEqx = Exists(new C("x'", Nat), x => equals(Nat,x,x) )

//-------important functions
var isEq0=FORALL(Prop,F=>FORALL(F,x=>Prop.equals(F,x,x)))
var isEq=FORALL(Type,F=>FORALL(F,x=>Type.equals(F,x,x)))
var isEq2=FORALL(Type1,F=>FORALL(F,x=>Type1.equals(F,x,x)))
var rfl0=Prop.rfl=AXIOM("rfl", isEq0) ; //rfl0.notation = type=>x=>"☯"+subscript(type)+"("+x+")"
var rfl=Type.rfl=AXIOM("rfl", isEq)  ; //rfl.notation = type=>x=>"☯'"+subscript(type)+"("+x+")"
var rfl2=Type1.rfl=AXIOM("rfl'", isEq2) ; //rfl2.notation = type=>x=>"☯''"+subscript(type)+"("+x+")"

//dependent type
var foo=y=> new ForAll(new C("x'", Nat), x => equals(Nat,x,y) ) 
//function as type:
var proof6 = AXIOM("proof6", FUN( Nat , y=>FUN(Nat , x=>equals(Nat,x,y) )     ) )
var forAllxEqA = FUN(Nat , foo)

var proof1 = AXIOM("proof1",forAllxEqx)

var proof2 = APPLY(proof1, y)

var addOne = FUN(Nat, z=>APPLY(succ,z) )

//-------------------------------------------------------------RULES--------------------------------------------------


//--------------------------------------------------Natural number Rules--------------------------------------------

//var plusRule = new Rule( [new C("_x", Nat), new C("_y", Nat)], x=>y=>succ( Nat.plus(x,y)) , x=>y=> Nat.plus(succ(x),y)   )
var plusRule2 = FUN(Nat, x => FUN(Nat, y=> Nat.equals( succ( Nat.plus(x,y))  ,   Nat.plus(succ(x),y)  )    ) )
var plusRule3 = FUN(Nat, x => FUN(Nat, y=> new Rule(   Nat.plus(x,succ(y)),  succ( Nat.plus(x,y))   )    ) )
var subRule = FUN(Nat, x => FUN(Nat, y=> new Rule(   Nat.sub(succ(x),succ(y)), Nat.sub(x,y))   )    ) 
var timesRule = FUN(Nat, x => FUN(Nat, y=> new Rule(   Nat.times(x,succ(y)),  Nat.plus( Nat.times(x,y) , x)   )    ) )

//var powerRule = FUN(Nat, x => FUN(Nat, y=> new Rule(   Nat.power(x,succ(y)),  Nat.times( Nat.power(x,y) , x)   )    ) )
var powerRuleT = FUN(Type, T=>FUN(T, x => FUN(Nat, y=> new Rule(   power(T,x,succ(y)),  times(T, power(T,x,y) , x)   )    ) ) )

//var powerOne = FUN(Nat, x => new Rule(  Nat.power(x,one), x  )  ) 
var powerOneT = FUN(Type, T=>FUN(T, x => new Rule(  power(T,x,one), x  )  )) 

var onePower = FUN(Nat, x => new Rule(  Nat.power(one,x), one  )  ) 

var addZero = FUN(Nat, x =>  new Rule(  Nat.plus(x,zero), x)    )
var addZeroL = FUN(Nat, x =>  new Rule(  Nat.plus(zero,x), x)   )   
var mulZero = FUN(Nat, x =>  new Rule(  Nat.times(x,zero), zero))  
var mulZeroL = FUN(Nat, x =>  new Rule(  Nat.times(zero,x), zero))  
var mulOne  = FUN(Nat, x =>  new Rule(  Nat.times(x,one), x)    )  
var mulOneL  = FUN(Nat, x =>  new Rule(  Nat.times(one,x), x)   )

function TIMES(x,y){
    var X=evalObject(x);
    var T=X.type;
    return times(T,X,y)
}
function PLUS(x,y){
    var X=evalObject(x);
    var T=X.type;
    return plus(T,X,y)
}

//----------------------------COMPLEX RULES-----------------------

var realPart = AXIOM("Re", FORALL(Type,F=>Complex(F).to(F))); realPart.notation = type=>x=>red("Re")/*+subscript(type)*/+""+x+""
var imPart = AXIOM("Im", FORALL(Type,F=>Complex(F).to(F))); imPart.notation = type=>x=>red("Im")/*+subscript(type)*/+""+x+""
var mod = AXIOM("modC", FORALL(Type,F=>Complex(F).to(F))); mod.notation = type=>x=>"|"+x+"|";
var norm = AXIOM("normC", FORALL(Type,F=>Complex(F).to(F))); mod.notation = type=>x=>"|"+x+"|^2";

//var realPartRule = FUN(Type , F=>FUN( F, re => FUN(F , im=>  new Rule( realPart(F,ComplexMk(F,re,im)), re )   )   ) )
//var imPartRule   = FUN(Type , F=>FUN( F, re => FUN(F , im=>  new Rule(   imPart(F,ComplexMk(F,re,im)), im )   )   ) )
var imPartProof   =  AXIOM("imPartProof",FORALL(Type, F=>FORALL(F, re=>FORALL(F, im=>equals(F, imPart(F,ComplexMk(F,re,im)), im )))))
var realPartProof =  AXIOM("realPartProof",FORALL(Type, F=>FORALL(F, re=>FORALL(F, im=>equals(F, realPart(F,ComplexMk(F,re,im)), re )))))
/*
var conjugate = AXIOM("conj", FORALL(Type, T=>T.to(T)))
var normCProof =   AXIOM("modCProof",FORALL(Type, F=>FORALL(Complex(F), z=>equals(F, norm(z),  times(Complex(F), z , conjugate(Complex(F),z ) )  ) )))
*/
//log("realPartRule",realPartRule)
function REALPART(F,x){ return realPart(F,x)}
function IMPART(F,x){ return imPart(F,x)}

var Eisen= AXIOM("F(ω)",Type.to(Type)) 
//Eisen.notation = x=>blue(bold("Q")+"(ω^3=1)")+"["+x+"]"
Eisen.notation = x=>x+"(ω)/\\langle ω^3=1\\rangle"
Eisen.mk = AXIOM("F(ω).mk", FORALL(Type, F=>F.to(F.to(Eisen(F)))))
Eisen.mk.notation = type=>x=>y=>"("+x+"+"+y+bold("ω")+")"
Eisen.zero = Eisen.mk(Int,0,0)
Eisen.omega = Eisen.mk(Int,0,1)
Eisen.one = Eisen.mk(Int,1,0)
Eisen.minusOne = Eisen.mk(Int,-1,0)
Eisen.omega2 =  Eisen.mk(Int,-1,-1)
Eisen.minusOmega2  = Eisen.mk(Int,1,1)
Eisen.minusOmega = Eisen.mk(Int,0,-1)

//(a+Wb)(c+Wd) = (ac-bd)+W(ad-bd+bc)


ComplexR = Complex(Real)
ComplexR.Exp =  FUN(Complex(Real), z=> ComplexMk(Real,
     Real.times( Real.Exp(realPart(Real,z) ), Cos(imPart(Real,z))  ) ,
     Real.times( Real.Exp(realPart(Real,z) ), Sin(imPart(Real,z))  )
))  

//var NatList = AXIOM("NatList",)

var complexAdd = FUN(Type, F=>FUN(Complex(F), x=> FUN(Complex(F), y=>  ComplexMk(F , plus(F, REALPART(F,x),REALPART(F,y)   ) ,
plus(F, IMPART(F,x),IMPART(F,y)   ) )))) 


var complexMul = FUN(Type, F=>FUN(Complex(F), x=> FUN(Complex(F), y=>  ComplexMk( F , sub(F,times(F, REALPART(F,x),REALPART(F,y)   ) ,
 times(F, IMPART(F,x),IMPART(F,y))  )  ,
plus(F,  times(F, REALPART(F,x), IMPART(F,y)), times(F, IMPART(F,x), REALPART(F,y))    )      )  )))


//try to prove it:
//var complexMulOp = AXIOM("ComplexMulOp" , complexMul(Nat).type)
//var cproof = FORALL(Complex(Nat), x=>FORALL(Complex(Nat), y=>equals(Complex(Nat), complexMulOp(x,y)  ,  complexMul(Nat,x,y)   )  ))


//var QuaternionPlus = FUN(Quaternion, x=>FUN(Quaternion, y=>APPLY4(QuaternionMk , Nat.plus(Q_RE(x),Q_RE(y) ) , Nat.plus(Q_I(x),Q_I(y) ),Nat.plus(Q_J(x),Q_J(y) ),Nat.plus(Q_K(x),Q_K(y) ))) )

//**COULD WE CREATE THIS AUTOMATICALLY**

var intARule = FUN(Nat, a=>FUN(Nat, b=>FUN(Nat, c=>FUN(Nat, d=>
new Rule( plus(Int, IntMk(a,b), IntMk(c,d))  , IntMk( Nat.plus(a,c), Nat.plus(b,d)       )   ) ))))
var intSRule = FUN(Nat, a=>FUN(Nat, b=>FUN(Nat, c=>FUN(Nat, d=>
    new Rule( sub(Int, IntMk(a,b), IntMk(c,d))  , IntMk( Nat.plus(a,d), Nat.plus(b,c)       )   ) ))))

var intMRule = FUN(Nat, a=>FUN(Nat, b=>FUN(Nat, c=>FUN(Nat, d=>
new Rule( times(Int, IntMk(a,b), IntMk(c,d))  , IntMk( Nat.plus(Nat.times(a,c),Nat.times(b,d)), Nat.plus(Nat.times(a,d),Nat.times(b,c))       )   ) ))))

var complexFProof = sorry(FORALL(Type, F=>FORALL(Complex(F), x=> FORALL(Complex(F), y=>
    equals(Complex(F), times(Complex(F),x,y)    , complexMul(F,x,y)  )))))

var complexARule = FUN(Type, F=>FUN(Complex(F), x=> FUN(Complex(F), y=>new Rule( plus(Complex(F),x,y)    , complexAdd(F,x,y)  ))))

//var rationalTimesRule = FUN(Rational, x=>FUN(Rational, y=>new Rule(  times(Rational, x,y)  , RationalMk( times(Rational,RatNum(x),RatNum(y)  )    ,  times(Rational,RatDen(x),RatDen(y)  )    )         ) ))
var rationalTimesProof = sorry(FORALL(Int, a=>FORALL(Int, b=>FORALL(Int, c=>FORALL(Int, d=>
equals(Rational, times(Rational, RationalMk(a,b) ,  RationalMk(c,d) ) ,   RationalMk( Int.times(a,c)    , Int.times(b,d)   )  ) )))))

var rationalDivideProof = sorry(FORALL(Int, a=>FORALL(Int, b=>FORALL(Int, c=>FORALL(Int, d=>
    equals(Rational, divide(Rational, RationalMk(a,b) ,  RationalMk(c,d) ) ,   RationalMk( Int.times(a,d)    , Int.times(b,c)   )  ) )))))
    

var rationalAddRule = FUN(Int, a=>FUN(Int, b=>FUN(Int, c=>FUN(Int, d=>
new Rule( plus(Rational, RationalMk(a,b) ,  RationalMk(c,d) ) ,   RationalMk(Int.plus(Int.times(a,d), Int.times(b,c))    , Int.times(b,d)   )  ) ))))

var rationalSubRule = FUN(Int, a=>FUN(Int, b=>FUN(Int, c=>FUN(Int, d=>
new Rule( sub(Rational, RationalMk(a,b) ,  RationalMk(c,d) ) ,   RationalMk( Int.sub(Int.times(a,d), Int.times(b,c))    , Int.times(b,d)   )  ) ))))

var rationalPowerProof = sorry(FORALL(Int, a=>FORALL(Int, b=>FORALL(Nat, n=>
    equals(Rational, power(Rational, RationalMk(a,b) ,  n ) ,   RationalMk(Int.power(a,n)   , Int.power(b,n)    )  ) ))))
    


//log("complexMul",complexMul)
//log("complexFRule",complexFRule)
//log("complexARule",complexARule)


var CNat = Complex(Nat)




//---------------RING SIMP------------------------------

//Nat.times(Nat.plus(x,y),Nat.plus(x,y))

//(x+y)*z = x*z+y*z
var distribL =  AXIOM("distribL",FORALL(Type,F=>FORALL(F,x=>FORALL(F,y=>FORALL(F,z=>equals(
    F,times(F,plus(F,x,y),z) ,    plus(F,times(F,x,z),times(F,y,z)) ))))))
var distribR =  AXIOM("distribR",FORALL(Type,F=>FORALL(F,x=>FORALL(F,y=>FORALL(F,z=>equals(
        F,times(F,x,plus(F,y,z)) ,    plus(F,times(F,x,y),times(F,x,z)) ))))))

var distribLM =  AXIOM("distribL",FORALL(Type,F=>FORALL(F,x=>FORALL(F,y=>FORALL(F,z=>equals(
    F,times(F,sub(F,x,y),z) ,    sub(F,times(F,x,z),times(F,y,z)) ))))))
var distribRM =  AXIOM("distribR",FORALL(Type,F=>FORALL(F,x=>FORALL(F,y=>FORALL(F,z=>equals(
        F,times(F,x,sub(F,y,z)) ,    sub(F,times(F,x,y),times(F,x,z)) ))))))

//---

//topology
//var Space =  AXIOM("Space",Type)
var Space=Type;
var sphere= AXIOM("sphere",Nat.to(Space)); sphere.notation = n=>blue("\\mathbb{S}")+"^{"+n+"}"
var ball =  AXIOM("ball",Nat.to(Space)); ball.notation = n=>blue("\\mathbb{B}")+"_{"+n+"}"
var boundary =  AXIOM("boundary", Space.to(Space)); boundary.notation = "\\partial"

var boundProp =  AXIOM("boundProp", FORALL(Nat, n=>Type1.equals(Space, boundary(ball(succ(n))), sphere(n)   )  ))






//---------------------------QUATERNION----------------------

//define the operators

var QpartRe =AXIOM(red("QRe"),FORALL(Type,F=>Quaternion(F).to(F)))
var QpartI = AXIOM(red("QI"), FORALL(Type,F=>Quaternion(F).to(F)))
var QpartJ = AXIOM(red("QJ"), FORALL(Type,F=>Quaternion(F).to(F)))
var QpartK = AXIOM(red("QK"), FORALL(Type,F=>Quaternion(F).to(F)))



//qRe{Nat}(x)
//define the rules for the operators
var qRe = FUN( Type, F=>FUN( F, re => FUN(F , imI=>FUN(F , imJ=>FUN(F , imK=>new Rule( QpartRe( F,QuaternionMk(F,re,imI,imJ,imK)), re))))))
//var qRe = newRule([F,F,F,F],  re=>imI=>imJ=>imK=>APPLY( QpartRe, APPLY4( QuaternionMk,re,imI,imJ,imK)), re))
var qI = FUN( Type, F=>FUN( F, re=>FUN(F , imI=>FUN(F, imJ=>FUN(F, imK=>new Rule(  QpartI(F, QuaternionMk(F,re,imI,imJ,imK)), imI))))))
var qJ = FUN( Type, F=>FUN( F, re=>FUN(F , imI=>FUN(F, imJ=>FUN(F, imK=>new Rule(  QpartJ(F, QuaternionMk(F,re,imI,imJ,imK)), imJ))))))
var qK = FUN( Type, F=>FUN( F, re=>FUN(F , imI=>FUN(F, imJ=>FUN(F, imK=>new Rule(  QpartK(F, QuaternionMk(F,re,imI,imJ,imK)), imK))))))
//shorthand



//-----------quaternion
Quaternion.plus = AXIOM("qplus" ,Quaternion.to(Quaternion.to(Quaternion)) )
Quaternion.fastValue=x=>"H["+x+"]"
var QuaternionPlus = AXIOM("QPlus",
    FORALL(Type,T=>
        FORALL(T,Ar=>FORALL(T,Ai=>FORALL(T,Aj=>FORALL(T,Ak=> 
        FORALL(T,Br=>FORALL(T,Bi=>FORALL(T,Bj=>FORALL(T,Bk=> 
        equals(Quaternion(T), plus(Quaternion(T), Quaternion.mk(T)(Ar,Ai,Aj,Ak), Quaternion.mk(T)(Br,Bi,Bj,Bk) ) ,
        Quaternion.mk(T)( plus(T,Ar,Br) ,plus(T,Ai,Bi), plus(T,Aj,Bj), plus(T,Ak,Bk) ))
        )))) )))) ))
//pattern matching version:
Quaternion.times = AXIOM("qtimes" ,Quaternion.to(Quaternion.to(Quaternion)) )
var QuaternionTimes = AXIOM("QTimes",
    FORALL(Type,T=>
        FORALL(T,Ar=>FORALL(T,Ai=>FORALL(T,Aj=>FORALL(T,Ak=> 
        FORALL(T,Br=>FORALL(T,Bi=>FORALL(T,Bj=>FORALL(T,Bk=> 
        equals(Quaternion(T), times(Quaternion(T), Quaternion.mk(T)(Ar,Ai,Aj,Ak), Quaternion.mk(T)(Br,Bi,Bj,Bk) ) ,
        Quaternion.mk(T)( 
            sub(T,times(T,Ar,Br), plus3(T, times(T,Ai,Bi), times(T,Aj,Bj), times(T,Ak,Bk)  )),
            sub(T,plus3(T, times(T,Ar,Bi), times(T,Ai,Br) , times(T,Aj,Bk)   ) , times(T,Ak,Bj)),
            sub(T,plus3(T, times(T,Ar,Bj), times(T,Aj,Br) , times(T,Ak,Bi)   ) , times(T,Ai,Bk)),
            sub(T,plus3(T, times(T,Ar,Bk), times(T,Ak,Br) , times(T,Ai,Bj)   ) , times(T,Aj,Bi))
    ))
)))) )))) )) 
//equivalent but function version:
/*
Quaternion.times = defineVar("QTimes",
    FUN(Type,T=>
        FUN(Quaternion(T), A=> FUN(Quaternion(T), B=> {
            var Ar = QpartRe(T,A); var Ai=QpartI(T,A); var Aj = QpartJ(T,A); var Ak=QpartK(T,A);
            var Br = QpartRe(T,B); var Bi=QpartI(T,B); var Bj = QpartJ(T,B); var Bk=QpartK(T,B);
        return Quaternion.mk(T)( 
            sub(T,times(T,Ar,Br), plus3(T, times(T,Ai,Bi), times(T,Aj,Bj), times(T,Ak,Bk)  )),
            sub(T,plus3(T, times(T,Ar,Bi), times(T,Ai,Br) , times(T,Aj,Bk) ) , times(T,Ak,Bj)),
            sub(T,plus3(T, times(T,Ar,Bj), times(T,Aj,Br) , times(T,Ak,Bi) ) , times(T,Ai,Bk)),
            sub(T,plus3(T, times(T,Ar,Bk), times(T,Ak,Br) , times(T,Ai,Bj) ) , times(T,Aj,Bi))
    )}) 
)))*/

//actually surreal numbers are sets a b {a|b}
var Sur = AXIOM("Surreal",Type); Sur.notation=bold("No")
Sur.mk =  AXIOM("Surreal.mk", Sur.to(Sur.to(Sur))); Sur.mk.notation = x=>y=>"\\{"+x+"|"+y+"\\}"
Sur.empty =  AXIOM("∅",Sur)


//HOMOMORPHISM of binary operator
var HomBin =  FUN(Type, A=>FUN(Type, B=>FUN( A.to(A.to(A)), binA=> FUN( B.to(B.to(B)), binB=>FUN( A.to(B), f=>FUN(A, x=>FUN(A,y=>
    equals(B, binB( f(x) , f(y) ) , f( binA( x,y)  )) 
 )))))))

HomBin.prop =  FORALL(Type, A=>FORALL(Type,  B=>FORALL( A.to(A.to(A)), binA=> FORALL( B.to(B.to(B)), binB=>FORALL( A.to(B) ,f=>FORALL(A,x=>FORALL(A,y=>
    equals(B, binB( f(x) , f(y) ) , f( binA( x,y)  )) 
 )))))))
//HomBin( Nat, Rat, plus(Nat), plus(Rat) , FUN(x=>Rat.mk(x,1) )
var HomAdd =  FORALL(Type, A=>FORALL(Type, B=> FORALL( A.to(B) ,f=>FUN(A, x=>FUN(A,y=>
    equals(B, plus(B, f(x) , f(y) ) , f( plus(A, x,y)  ))
)))))



// Eq.rfl : forall(x:a) (x = x)
//rfl forall(t:Type), a Eq.rfl x

function log(n,x){
    tempNum=0
    print(normal(n)+" = "+fill(x.toString()) +" : " +typeOf(x))
   // print(bold(equiv(x,x)))
}

/*
var B0 = times(Complex(Nat), ComplexMk(Nat,two,two) , ComplexMk(Nat,one,three)  )
B0 = times(Complex(Rational), ComplexMk(Rational,RationalMk(1,3),RationalMk(2,3)) , ComplexMk(Rational,RationalMk(1,2),RationalMk(1,5))  )
//B0 = times(Complex(CNat), ComplexMk(CNat,ComplexMk(Nat,1,3),ComplexMk(Nat,2,3)) , ComplexMk(CNat,ComplexMk(Nat,1,2),ComplexMk(Nat,1,5))  )



log("calc0",B0)
//var B1 = RW(B0,[complexFRule])
//log("calc", B1 )

var B4 = SIMP(B0,1,true)
log("simp", B4)
*/

/*
log("zero",zero)
log("one",one)
log("two",two)
log("four",four)
log("succ",succ)
log("plus",plus)
log("twoPlusTwo",twoPlusTwo)
log("twoEqualsOnePlusOne",twoEqualsOnePlusOne)

log("NatToNat",Nat.to(Nat))
log("Nat",Nat)

log("Complex",Complex)

log("one_two",one_two)
log("one_two_three",one_two_three)
log("Nat_Nat",Nat_Nat)

log("funnyTwo",funnyTwo)

log("forAllxEqx",forAllxEqx)
log("existsxEqx",existsxEqx)
//log("forAll2E1P1",forAll2E1P1)
log("proof1",proof1)
log("proof2",proof2)

log("addOne",addOne)

log("forAllxEqA",forAllxEqA)
log("forAllxEqA Y", APPLY(forAllxEqA,y))
*/
function proved(prop,proof){
    if( proof.type.toString()===prop.toString()){
        return prop.toString()+" = "+green(bold("True"))
      +red(bold(" Q.E.D "));
    }else{
        return  prop.toString()+" != <br>"+proof.type.toString()
        + bold(" Not proved!" )
    }
}

/*

log("addOne two", APPLY(addOne, APPLY(addOne,two)))
log("proof6", proof6)
log("proof6", APPLY( proof6 , one))

log("rfl",rfl)

var dp = new Intro(one, rfl(Nat) )
log("proof1eq1",dp)
print(proved(existsxEqx,dp))

log("PROOF2eq2", APPLY(rfl(Nat), two)) 
log("plusRule",plusRule2)
log("plusRule23", APPLY(APPLY(plusRule2, two), three))
//log("plusRule",plusRule)
log("plusRule3",plusRule3)
log("addZero",addZero)
log("complex3_4", complex3_4)
log("rational2_3",rational2_3)
log("sqrt_2",sqrt_2)
log("quaternion1234",quaternion1234)
print("OK")
print(equiv(three,two))
print(replace(four, one, y))
print(replaceUsing(four, new Rule(one,y) ))
log("newrule", plusRule3(one,one))
var A0=Nat.plus(two,two)
print(A0)
//var A1=replaceUsing( A0 , APPLY2(plusRule3,two,one) ) 
var A1=replaceUsing( A0 , plusRule3 ) 
print( A1 )
var A2=replaceUsing( A1 , plusRule3)//apply(APPLY(plusRule3,two),zero) ) 
print(A2)
var A3 = replaceUsing( A2 , addZero)//apply( addZero, two) )
print(A3)
//print( replace( Nat.plus(two,two) ,   ) )
 
var twoPlusTwo = Nat.plus( two ,two )
var onePlusOne = Nat.plus( one ,one )
var twoEqualsOnePlusOne = equals( Nat, two, onePlusOne)
var forallNat = AXIOM("∀",Nat.to(Prop.to(Prop)))


var Fermat = new ForAll( new C("x'",Nat),x=> new ForAll( new C("y'",Nat),y=>new ForAll( new C("z'",Nat),z=>new ForAll( new C("n'",Nat),n=>
    Nat.equals(  Nat.plus( Nat.power(x,n), Nat.power(y,n) ),  Nat.power(z,n) )))))  
log("Fermat",Fermat)

*/

//-----------natural numbers game-----
//3=3
//log("3=3 proof " , rfl(Nat,3)   )

var TWO = AXIOM("TWO",Nat)
var ONE = AXIOM("ONE",Nat)
var prop1  = sorry(equals(Nat,TWO,succ(succ(zero)) )) //by def
var prop2  = sorry(equals(Nat,succ(succ(zero)), TWO )) //by def
var lemma1 = AXIOM("lemma1",equals(Nat,TWO,succ(ONE))) //by def
var lemma2 = AXIOM("lemma2",(equals(Nat,ONE,succ(zero))))

var proof9 = RW2( prop1.type,[lemma1,lemma2] )

//var proof10 = RW2( rfl(Nat)(TWO).type,[lemma1,lemma2])

function define(N,M){
    return equals(M.type,  AXIOM(N,M.type), M )
}

/*
P:A->Prop ,   C:P(a)  , B:a=b
------------------------------------
          rw{P,b} : P(b)
*/




//print("OK2")

/*
//General Realtivity
g = AXIOM(x=>y=>"g_{"+x+" "+y+"}", Zmod(4).to(Zmod(4).to( Euc(4).to(R))))
mu = AXIOM("\\mu",Zmod(4))
nu = AXIOM("\\nu",Zmod(4))
x = AXIOM("x", Euc(4))
g(mu,nu)(x)


*/

//---------------LOGIC--------------------



//false -> true
//FUN(False, x=> True.intro)///:False->True

//true -> false **NOT POSSIBLE**

//True and False --> False
//AND = FUN(And(True,False),x=>   )//True&False -->False
//True OR False --> True
//OR  = FUN(Or(True,False),x=>left(True.intro) )//True OR False --> True

//var left = FUN(Type, t=> FUN(T, x => 

//-------------------------OR------------------------------------

Prop.or  =  AXIOM("propOr",Prop.to(Prop.to(Prop)));     Prop.or.notation  = x=>y=>"("+x+"∨"+y+")"
Type.sum =  AXIOM("typeSum",Type.to(Type.to(Type)));    Type.sum.notation = x=>y=>"("+x+"+"+y+")"

//left (B) (x:A) : sumType(A,B)
//right(B) (x:A) : sumType(A,B)
//(left) :    A->Sum(A,B)
//(right):    B->Sum(A,B)

Type.left  =  AXIOM("left", FORALL(Type, A=>FORALL(Type, B =>A.to(Type.sum(A)(B)))))
Prop.left  =  AXIOM("leftOr",FORALL(Prop, A=>FORALL(Prop, B =>A.to(Prop.or(A)(B))) )); Prop.left.notation = A=>B=>C=>"("+C+")"+subscript(A+"\\rightarrow"+"("+A+"∨"+B+")" )
Prop.right =  AXIOM("right", FORALL(Type, A=>FORALL(Type, B =>B.to(Type.sum(A)(B)))))
Type.right =  AXIOM("rightOr",FORALL(Prop, A=>FORALL(Prop, B =>B.to(Prop.or(A)(B))) ))

//------------------------AND------------------------

Prop.and  = AXIOM("prodType",Prop.to(Prop.to(Prop))); Prop.and.notation = x=>y=>"("+x+"∧"+y+")"
Type.prod = AXIOM("prodType",Type.to(Type.to(Type))); Type.prod.notation  = x=>y=>"("+x+"×"+y+")"

//(pairs) (What is pair of propositions called?)
Prop.pair= AXIOM("propPair", FORALL(Prop,A=>FORALL(Prop,B=>A.to(B.to(Prop.and(A,B)))))); Prop.pair.notation = a=>b=>x=>y=> "("+x+","+y+")"
Type.pair = AXIOM("prodMk", FORALL(Type,A=>FORALL(Type,B=>A.to(B.to(Type.prod(A,B)))))); Type.pair.notation = a=>b=>x=>y=> "("+x+","+y+")"//+subscript(a+"×"+b)
Type.First  =AXIOM("first",   FORALL(Type,A=>FORALL(Type,B=>Type.prod(A)(B).to(A))));      Type.First.notation = a=>b=>x=>"{"+x+"}"+subscript("L")
Type.Second =AXIOM("second",  FORALL(Type,A=>FORALL(Type,B=>Type.prod(A)(B).to(B)) ));     Type.Second.notation = a=>b=>x=>"{"+x+"}"+subscript("R")



//var isPrime=AXIOM("isPrime", FORALL(Nat,P=> FORALL(Nat,A=> FORALL(Nat, B=>  Nat.equals(P, Nat.times(A,B)  ).to(  
//    Prop.and( Prop.or( Nat.equals(A,1), Nat.equals(B,1)  )  , Nat.gt(P,1) ))) )))  
var isPrime = defineVar("isPrime", FUN(Nat,P=>FORALL(Nat,A=> FORALL(Nat, B=>  Nat.equals(P, Nat.times(A,B)  ).to(  
        Prop.and( Prop.or( Nat.equals(A,1), Nat.equals(B,1)  )  , Nat.gt(P,1) ))) ))) 
isPrime.fastValue = p=>{
    if(p<=1) return false;
    for(var i=2; i<Math.sqrt(p)+1;i++){
        if(p%i==0) return false;
    }
    return true;
}




//----------------------Complex functions-----------------
//var C=Complex
//Real.Sin
var CR=Complex(Real);CR.notation = blue("\\mathbb{C}");
var HR=Quaternion(Real);HR.notation = blue("\\mathbb{H}");
var OR=Octonion(Real);OR.notation = blue("\\mathbb{O}");
//defineVar(blue("\\mathbb{C}"),Complex(Real));
CR.mk = Complex.mk(Real)

CR.power=AXIOM("CR.power",CR.to(CR.to(CR))  ); CR.power.notation = z=>w=>z+"^{"+w+"}"
CR.one = CR.mk(Real.one,Real.zero);
var infty = AXIOM("\\infty", Nat)
//var zeta = defineVar("zeta", FUN(CR, z=> sum(CR, FUN(Nat, n=> CR.power( CR.mk(Real.fromRat(Rat.mk(Int.mk(n,0),Int.one)) ,Real.zero)  ,   z) ), infty )   ) ,"\\zeta")

var CDerivT = AXIOM(x=>"CDeriv",FORALL(Type, T=>CR.to(T).to(CR.to(T))))
CDerivT.notation = DerivT.notation


var CTimes = z=>w=> [z[0]*w[0]-z[1]*w[1], z[0]*w[1]+z[1]*w[0] ] 

var CR2CR = CR.to(CR);

CR.Id = AXIOM("CId",CR.to(CR)); CR.Id.fastValue = z=>z;
CR.Sin = AXIOM("CSin",CR.to(CR) );CR.Sin.fastValue = z=>[Math.sin(z[0])*Math.cosh(z[1]), Math.cos(z[0])*Math.sinh(z[1])]
CR.Cos = AXIOM("CCos",CR.to(CR) );CR.Cos.fastValue = z=>[Math.cos(z[0])*Math.cosh(z[1]), -Math.sin(z[0])*Math.sinh(z[1])]
CR.Tan = AXIOM("CTan",CR.to(CR) );CR.Tan.fastValue = z=>{ var d=Math.cos(2*z[0])+Math.cosh(2*z[0]);  return [Math.sin(2*z[0])/d,   Math.sinh(2*z[1])/d]}
CR.Exp = AXIOM("CExp",CR.to(CR) );CR.Exp.fastValue = z=>{ var e=Math.exp(z[0]); return [e*Math.cos(z[1]),e* Math.sin(z[1])]}
CR.Sqrt = AXIOM("CSqrt",CR.to(CR) );CR.Sqrt.fastValue = z=>{ var r=Math.pow(z[0]**2+z[1]**2,0.25);var theta = Math.atan2(z[1],z[0]); return   [Math.cos(theta/2), Math.sin(theta/2)]}

//****cheats****
//FUN(CR,z=>iter(CR, FUN(CR, x=> plus(CR,square(CR,x),z) ) , z , 10) ) (Complex.mk(Real,3,4))
CR.times = AXIOM("ctimes",CR.to(CR.to(CR))); CR.times.fastValue = z=>w=> [z[0]*w[0]-z[1]*w[1], z[0]*w[1]+z[1]*w[0] ] ;
CR.plus = AXIOM("cplus",CR.to(CR.to(CR))); CR.plus.fastValue = z=>w=> [z[0]+w[0],z[1]+w[1]];
CR2CR.times =AXIOM("c2ctimes",CR2CR.to(CR2CR.to(CR2CR))); CR2CR.times.fastValue = f=>g=>x=>CR.times.fastValue( f(x))( g(x) ) 
//FUN(CR,z=>iter(CR, FUN(CR, x=> CR.plus(CR.times(CR,x,x),z) ) , z , 10) ) (Complex.mk(Real,3,4))

Complex.fastTimes = t=>z=>w=> [z[0]*w[0]-z[1]*w[1], z[0]*w[1]+z[1]*w[0] ];

//true for Re(z)>0
//Dirchlect deta
var deta = defineVar("deta", FUN(CR, z=> sum(CR, FUN(Nat, n=>times(CR, CR.mk(  Real.fromRat( power(Rat,-1,n)),  Real.zero  ) ,CR.power( CR.mk(Real.fromRat(Rat.mk(Int.mk(n,0),Int.one)) ,Real.zero)  ,   z) )), infty )   ) ,"\\eta")
var zeta = defineVar("zeta", FUN(CR,z => divide(CR, deta(z), sub(CR, CR.one   ,  CR.power( CR.mk( Real.fromRat(2), Real.zero ) , sub(CR, z, CR.one  )            )          )       )   )  , "\\zeta");
//f
//a=b
//proof:f(a)
//----------
//f(b)

//Functional Derivative:

var DFunc = AXIOM("DFunc" , (R2R.to(R2R)).to(R2R.to(R))  )
DFunc.notation = a=>f=>x=>"\\frac{\\delta}{\\delta "+f+"("+x+")}"+a+"("+f+")("+x+")";


var subst = AXIOM("subst", FORALL(Type,N=>FORALL(N,a=>FORALL(N,b=>FORALL(N.to(Prop),F=> 
    Type.equals(N,a,b).to(F(a).to(F(b)))  
)))))//error doing forall over functions?
subst.notation = N=>a=>b=>f=>AeqB=>fa=>"\\left[\\frac{"+fa +"◀" + AeqB +"}{"+fill(fa.toString())+"}\\right]"


var intro = AXIOM("intro", FORALL(Type, T=>FORALL(T,t=> FORALL(T.to(Prop), F=>FORALL(T,x=>F(x)).to( F(t) ) ) )  )  ) 

intro.notation = t=>item=>func=>premise=>"("+premise+"◀" + item+")"

var VO = AXIOM("VO",Type) //vectorspace

VO.one = AXIOM("VO.one",VO); VO.one.notation = "\\mathbb{1}"
VO.zero = AXIOM("VO.zero",VO); VO.zero.notation = "\\mathbb{0}"
VO.times = AXIOM("VO.times",Complex(Real).to(VO.to(VO.to(VO)))  ); VO.times.notation = z=>x=>y=>"("+x+"\\otimes_{"+z+"}"+y+")"
VO.trans = AXIOM("VO.T", VO.to(VO));VO.trans.notation = "T";
//myintro(human)(socrates)(isMortal)(premise) /// isMortal(t)

//Virosoro
var Vir = AXIOM("Viro",Type)
Vir.central = AXIOM("1", Vir);
Vir.mk = AXIOM("vir.mk",R2R.to(Vir)); Vir.mk.notation=f=>"L_{"+f+"}"


//----Elliptic group----
var EllipticC = AXIOM("EC",FORALL(Type,T=> T.to(T.to(Type)  ))  );EllipticC.notation = T=>a=>b=>"E_{"+a+","+b+"}["+T+"]"
EllipticC.mk = AXIOM("ElipMK" , FORALL(Type,T=>FORALL(T,a=>FORALL(T,b=>FORALL(T,x=>FORALL(T,y=>EllipticC(T)(a,b)))))))
EllipticC.mk.notation = T=>a=>b=>x=>y=>"("+x+","+y+")_{E_{"+a+","+b+"}}"

var Eop = AXIOM("eplus" , FORALL(Type, T=>T.to(T.to(T)) )) ; Eop.notation = T=>x=>y=>"("+x+"\\otimes_E"+y+")"


//Using Complex as a stand in for R2 (Complex structure probably not needed!)
var eplusProp = AXIOM("eplusProp",
    FORALL(Type,T=>
        FORALL(T,x1=>FORALL(T,y1=>FORALL(T,x2=>FORALL(T,y2=>{
            var lambda = divide(T, sub(T, y2,y1 ), sub(T, x2,x1)   )
            var lambda2 = times(T,lambda,lambda)
            var lambda3 = times(T,lambda2,lambda)
            return equals( Complex(T) ,
            Eop( Complex(T) , Complex.mk(T)(x1,y1) , Complex.mk(T)(x2,y2)   ),
        Complex.mk(T)(                  
                sub(T,sub(T, lambda2, x1),x2) // lambda^2 - x1 - x2
            ,   sub(T,sub(T,times(T, lambda, plus(T, x2 , plus(T,x1,x1)  )   ), lambda3),y1)
                        //-lambda (lambda^2 - 2*x1 - x2)  - y1 )  = -L^3 + 2 * L*x1 + L*x2 - y1 //  (lambda)*(x2) = (y2-y1) + lambda*x1
                            )
    )}
    ))))))

var ellipticPlusProp = AXIOM("ellipticPlusProp",
    FORALL(Type,T=>
        FORALL(T,a=>FORALL(T, b=>
        FORALL(T,x1=>FORALL(T,y1=>FORALL(T,x2=>FORALL(T,y2=>{
            var lambda = divide(T, sub(T, y2,y1 ), sub(T, x2,x1)   )
            var lambda2 = times(T,lambda,lambda)
            var lambda3 = times(T,lambda2,lambda)
           return equals( EllipticC(T)(a,b) ,
        plus( EllipticC(T)(a,b) , EllipticC.mk(T)(a,b)(x1,y1) , EllipticC.mk(T)(a,b)(x2,y2)   ),
        EllipticC.mk(T)(a,b)(                  
               sub(T,sub(T, lambda2, x1),x2) // lambda^2 - x1 - x2
            ,  sub(T,sub(T,times(T, lambda, plus(T, x2 , plus(T,x1,x1)  )   ), lambda3),y1)
                       //-lambda (lambda^2 - 2*x1 - x2)  - y1 )  = -L^3 + 2 * L*x1 + L*x2 - y1 //  (lambda)*(x2) = (y2-y1) + lambda*x1
                            )
    )}
    ))))))))



var exists = AXIOM("Exists", FORALL(Type, T=>T.to(Prop).to(Prop) )); exists.notation = (T,t)=>(F,y)=>{
    var n=new C(getNewVariName(),t);
    if (typeof y =='function')
        return "\\bigvee\\limits_{"+n+":"+T+"}" + y(n) 
    else if(y.kind=="fun"){
        return "\\bigvee\\limits_{"+n+":"+T+"}(" + y.apply(n) + ")" // makeshift
    }else{
        return "\\bigvee\\limits_{"+n+":"+T+"}(" + F + ")" //
    }
}
//  P(x:T) -> Exists(y:T),P(y) 
exists.mk = AXIOM("use",FORALL(Type,T=>FORALL(T, x=>FORALL(T.to(Prop), P=>P(x).to(exists(T,P))) ) ))
//exists.mk(Nat)(3)( FUN(Nat,x=>equals(Nat,x,3)))(rfl(Nat,3))

var Exists = function(t, f){
    return exists(t, FUN(t,f) );
}

//delta(x)  =1 if  x=0 or 0 otherwise = sin(pi x)/(pi x)
var delta = AXIOM("\\delta",FORALL(Type, T=>T.to(Nat)));delta.notation = T=>x=>"\\delta_{"+T+"}("+x+")"
delta.fastValue = t=>x=> x==0?1:0; //not true for modular arithmetic
//for Zmod(n) the formula is delta(x) = sin(pi*x)/(n*sin(pi*n))


var conditional = AXIOM("conditional", FORALL(Type,T=>T.to(Prop).to(Type)  ) ); conditional.notation = (T,t)=>(p,y)=>{
    var n=new C(getNewVariName(),t);  
    if(typeof y =='function') return "\\left\\{"+n+"\\in"+T+" \\middle| "+ y(n) + "\\right\\}"
    else return "\\left\\{"+T+" \\middle| "+ p + "\\right\\}"
}
conditional.mk = AXIOM("conditional.mk" , FORALL(Type, T=>FORALL(T.to(Prop),P=>FORALL(T, x=> P(x).to(conditional(T,P)  )  )  )))
conditional.mk.notation = t=>p=>x=> {
    var n=new C(getNewVariName(),t); 
    return "\\left\\{"+n+"\\in"+t+" \\middle| "+ p + "\\right\\}.mk("+x+")";
}

var Prime = defineVar("Prime",conditional(Nat,FUN(Nat,x=>isPrime(x))));

//===================================GRAPHICS=============================

var Circle = AXIOM("◯",Type)
Circle.mk = AXIOM("◯", Real.to(Real.to(Real.to(Circle))))
Circle.mk.fastValue = r=>x=>y=> { 
    dc.fillStyle="red"
    dc.beginPath();
    dc.arc(x, y, r, 0, 2 * Math.PI); 
    dc.fill();
    return 99;}

var Square = AXIOM("□",Type)
Square.mk = AXIOM("□", Real.to(Real.to(Real.to(Square))))
Square.mk.fastValue = r=>x=>y=> { 
    dc.fillStyle="red"
    dc.beginPath();
    dc.rect(x-r/2,y-r/2,r,r)
    dc.fill();
    return 99;}

var Shape= AXIOM("Shape",Type)
Shape.of = AXIOM("ShapeOf", FORALL(Type, T=>T.to(Shape))); Shape.of.notation=t=>"Shape::"

var Animal = NewType("Animal")
var Cat = NewType("Cat")
var is = AXIOM("is", Type.to(Type.to(Prop)))
Cat.isAnimal = AXIOM("catIsAnimal",is(Cat,Animal) )  //AXIOM
var Rock = NewType("Rock")
Cat.mk = AXIOM("Cat.mk",Cat)
Rock.mk = AXIOM("Rock.mk",Rock)
var Dog = NewType("Dog")
var cast = AXIOM("cast", FORALL(Type,T=>FORALL(Type,U=>is(T,U).to(T.to(U) ) ))) //cast only if we can
var isAnimal = AXIOM("isAnimal",FORALL(Type, T=>T.to(Prop) ))
Animal.of = AXIOM("AnimalOf", FORALL(Type,T=>is(T,Animal).to( T.to(Animal) )))
Animal.ofCat = defineVar("AnimalOfCat",Animal.of(Cat)(Cat.isAnimal) )
//Animal.ofCat = AXIOM("AnimalOfCat",CAST(Animal,Cat))

//Real.is(Field)
//times(Q,isField(Q),A,B)


/*
isEqual2 = FUN(Nat,x=>Nat.equals(x,2))
isTwoType=conditional(Nat)(isEqual2);
isTwoType.mk = conditional(Nat)(isEqual2);
conditional.mk(Nat)(isEqual2)(2)(rfl(Nat)(2) );
isTwoType.mk(2)(refl(Nat)(2));
*/

//exists(Nat)(FUN(Nat,x=>lt(Nat,x,3)))


//True AND True
//prodMk0(True)(True)(True.intro)(True.intro)

//True OR False
//left0(True)(False)(True.intro)
USE_MATHJAX=true

console.log("Definitions loaded")
document.write("\\(\\textcolor{red}{OK}\\)")


//format nicer arrays

Array.prototype._originalToString = Array.prototype.toString;

// Override the toString method for all arrays
Array.prototype.toString = function() {
    return '[' + this.join(', ') + ']';
};




//-----programming----
var instruct=AXIOM("instruct",Type)
var mystring=AXIOM("string",Type); 
mystring.fromNat =AXIOM("mystring.fromNat",Nat.to(mystring)); mystring.fromNat.fastValue = n=>n.toString(); 
mystring.fromNat.notation=x=>"''"+x+"''";
var println=AXIOM("println",mystring.to(instruct)); println.fastValue = s=>{ print(s); }


//-------------Lie groups and Lie algebras------------
//(Could do group quotients)
//Could to rank and number of generators
var LieGroup = AXIOM("LieGroup",Type) //Type2?
var SU = AXIOM("SU",Nat.to(Type))
var Orthog = AXIOM("Orthog",Nat.to(Type));Orthog.notation="O";
var SO = AXIOM("SO",Nat.to(Type));
var Sp = AXIOM("Sp",Nat.to(Type))
var E8 = AXIOM("E_8",Type)
var E7 = AXIOM("E_7",Type)
var E6 = AXIOM("E_6",Type)
var F4 = AXIOM("F_4",Type)
var G2 = AXIOM("G_2",Type)
var LieAlgebra = AXIOM("LieAlg",Type.to(Type) )

Real.Step = AXIOM("step", Real.to(Real)); Real.Step.notation="H"; Real.Step.fastValue = x=>(x>0?1:0);

Real.Random = AXIOM("random", Nat.to(Real)); Real.Random.fastValue = x=> Math.random()

//------------Multi Arrays--------------------
var MultiArray=AXIOM("Array", FORALL(Type,T=>List(Nat).to(Type) ) );
MultiArray.notation= T=>L=>{
    return T+"^{"+L+"}";
}
MultiArray.fromList = AXIOM("ArrayfromList",FORALL(Type,T=>FORALL(List(Nat),shape=> List(T).to(MultiArray(T,shape)) )))
MultiArray.fromList.notation = t=>shape=>list=> "{"+list+"}"+subscript(shape);
MultiArray.fromList.fastValue = t=>shape=>list=>{
    return list;
    //return {shape:shape,list:list};
};

function arrayProd(L){
    var r=1;
    for(var i=0;i<L.length;i++){
        r*=L[i];
    }
    return r;
}

//MultiArray.shape = AXIOM("Shape", FORALL(Type, T=>FORALL(List(Nat), shape=>MultiArray(T,shape).to(List(Nat)))))

//MultiArray.fromFuncV = AXIOM("MAfromFuncV",FORALL(Type, T=>FORALL(List(Nat),shape=>Vector(T,List.Length(Nat,shape)).to(T).to(MultiArray(T,shape )) )   ) )
MultiArray.fromFuncL = AXIOM("ArrayfromFuncL",FORALL(Type, T=>FORALL(List(Nat),shape=>(List(T).to(T)).to(MultiArray(T,shape )) )   ) );
MultiArray.fromFuncL.fastValue = t=>shape=>f=>{
    var result = new Array(arrayProd(shape))   
    //console.log(f)
    if(shape.length==3){
        var n=0;
        for(var x=0;x<shape[0];x++){
            for(var y=0;y<shape[1];y++){
                for(var z=0;z<shape[2];z++){     
                    result[n++] = f( [x,y,z]  );
                }
            }
        }
    }
    return result;
}

function applyToList(input,F){
    var result = new Array(input.length) 
    for(var n=0;n<result.length;n++){
        result[n] = F(input[n])
    }
    return result;
}

MultiArray.get = AXIOM("NDget", FORALL(Type, T=>FORALL( List(Nat), shape=>List(Nat).to(MultiArray(T,shape).to(T) ))));
MultiArray.get.fastValue = t=>shape=>index=>L=>{
    var result=0;
    var a=0;
    for(var i=0;i<index.length;i++){
       if(i>0) a*=shape[i-1];
        a+=index[i];
    }
    return L[a];
}

//should clone array?
MultiArray.set = AXIOM("NDset", FORALL(Type, T=>FORALL( List(Nat), shape=>List(Nat).to(T.to(MultiArray(T,shape).to( MultiArray(T,shape) ) )))));
MultiArray.set.fastValue = t=>shape=>index=>val=>L=>{
    var result=0;
    var a=0;
    for(var i=0;i<index.length;i++){
       if(i>0) a*=shape[i-1];
        a+=index[i];
    }
    L[a] = val;
    return L;
}
/*
a=MultiArray.fromList(Nat,LIST(2,2),LIST(1,2,3,4));
MultiArray.get(Nat, LIST(2,2), LIST(0,0), a )  
*/

//array functions
MultiArray.Tanh = AXIOM("NDTanh",FORALL(Type,T=>FORALL(List(Nat),shape=> MultiArray(T,shape).to(MultiArray(T,shape)) )));
MultiArray.Tanh.fastValue = T=>shape=>input=>applyToList(input,Math.tanh)
MultiArray.Random =AXIOM("NDRandom", FORALL(Type,T=>FORALL(List(Nat),shape=> MultiArray(T,shape))));
MultiArray.Random.fastValue = T=>shape=>{
    var input=new Array(arrayProd(shape));
    return applyToList(input,Math.random)
}

var Video = AXIOM("Video",Type); Video.notation = "🎥"
Video.width=AXIOM("Video.Width" , Video.to(Nat)); Video.width.fastValue = v=>v.videoWidth;
Video.height=AXIOM("Video.Height" , Video.to(Nat)); Video.height.fastValue = v=>v.videoHeight;
Video.frame=AXIOM("Video.Frame", FORALL(Video,v=> Nat.to(MultiArray(Float32,LIST(1,3,Video.height(v),Video.width(v))) )));
Video.frame.fastValue = video=>frame=>{
    var canvas=document.getElementById("hiddencanvas")
    var context = canvas.getContext("2d")
    video.currentTime = frame/30;
    canvas.width = video.videoWidth;
    canvas.height = video.videoHeight;
    context.drawImage(video, 0, 0, canvas.width, canvas.height);
    const imageData = context.getImageData(0, 0, canvas.width, canvas.height);
    const data = imageData.data;
    //need to convert to RGB
    return data;
}

var LoadVideo = AXIOM("LoadVideo",Nat.to(Video));
LoadVideo.fastValue = _=>{ document.getElementById("videoFileInput").click(); return 0;}

//a= MultiArray.Random(Real, LIST(3,50,50)) ;
//plotBitmap(3,50,50,a.float())
//A^ijk B^lmn
MultiArray.TensorProd = AXIOM("TensorProd",  FORALL(Type,T=>FORALL(List(Nat),shape1=>FORALL(List(Nat),shape2=>
    MultiArray(T,shape1).to(MultiArray(T,shape2).to( MultiArray(T, List.Concat(Nat,shape1,shape2 )  )  ))))))
//MultiArray.Dot = AXIOM("NDDot",  FORALL(Type,T=>FORALL(List(Nat),shape1=>FORALL(List(Nat),shape2=>MultiArray(T, ContractedShape(shape1,shape2 )  )  )




var NDReverse = AXIOM("NDReverse", FORALL(Type, T=>FORALL(List(Nat),shape=> Nat.to(MultiArray(T,shape).to(MultiArray(T,shape) ) )  )))
NDReverse.fastValue = t=>shape=>index=>L=>{
    //we want to reverse tensor at index L
    var result=new Array(arrayProd(shape))
    //console.log(L)
    reverseArray(0,index,shape,L,result,0);
    return result;
}
NDReverse.notation = t=>shape=>"NDReverse";

// (2,2)  [[1,2],[3,4]]
//ONLY WORKS for last index:
function reverseArray(i,index,shape,L,result,offset){ //[[[1,2],[4,5]], [[5,6],[7,8]]  ]
    //console.log(i+" "+offset)
    if(i==shape.length-1){
        if(i==index)for(var x=0;x<shape[i];x++) result[offset+x] = L[offset+shape[i]-1-x];
        else 
        for(var x=0;x<shape[i];x++) result[offset+x] = L[offset+x];
        //result.splice(offset, shape[i], ...L.slice(offset, offset + shape[i]));
        offset+=shape[i];
    }else{
        for(var x=0;x<shape[i];x++) offset = reverseArray(i+1,index,shape,L,result,offset);
    }
    return offset;
}



//NDReverse(Nat,LIST(2,2,2),2, MultiArray.fromList(Nat,LIST(2,2,2),toList([1,2,3,4,5,6,7,8],Nat) ))

Vector.fromList = AXIOM("VfromL", FORALL(Type, T=>FORALL(List(T), L=>Vector(T,List.Length(T,L) ) ) ) )
Vector.fromList.notation = t=>L=>L;
Vector.fromList.fastValue = t=>L=>L;

//group theory
var Aut = AXIOM("Aut", Type.to(Type));
//equals(Type, Aut(Griess) , Monster) //Monster-Lie group
//equals(Type, Aut(Octonion) , G2)
//equals(Type, Aut(Quaternion) , SO(3))
//equals(Type, Aut(Complex), U(1))


//--------------------------Physical constants
var MeV=8.190746095061798E-23; //in planck units
var Me = AXIOM("m_e",Real);  Me.fastValue = 0.51099895069*MeV
var Mmu = AXIOM("m_\\mu",Real);  Mmu.fastValue = 105.6583755*MeV
var Mtau = AXIOM("m_\\tau",Real); Mtau.fastValue = 1776.9*MeV
var FineStructure = AXIOM("\\alpha",Real); FineStructure.fastValue = 1/137.035999177;


var Input = AXIOM("Input",FORALL(Type, t=>t)); Input.fastValue = t=> prompt("Enter a number");

//imperitive programming

Nat.set = AXIOM("Nat.Set", Nat.to(Nat.to(Nat))); Nat.set.fastValue = (_,x)=>y=>{
    console.log(x,y)
    x.fastValue = y;
    return y;
}
Nat.set.notation = x=>y=> x +":="+ y;