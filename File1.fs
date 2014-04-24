module divTest

open System
open System.Numerics
open System.Collections.Generic
open Microsoft.FSharp.Math
//open FsCheck
module matrixG=Matrix.Generic
type listMonadBuilder()=
        member x.Bind(comp,func)= comp|>List.map(fun x->func x)|> List.concat
        member x.Return(comp)=[comp]


//[<CustomComparison>]
//type abcTriplet (ain,bin,cin)=
//    member this.(a,b,c)=(ain,bin,cin)
//    interface System.IComparable with
//        override  x.CompareTo(y)=
            
let mod2Test a b c= 0=((1+a+b+c) % 2)
let mod3Test a b c= (2=b%3) && (0=(a+c)%3)
let mod4Test a b c=
    match a%4 with
    |x when ((x=0)||(x=2))->( 0=( (a+c)%4) && (3=b%4) )   ||( (2=(a+c)%4)&&(1=b%4) )
    |_->false 
let mod8Test a b c=
    match (a%8,b%8,c%8) with
    |x when x=(6,3,6)->true
    |x when x=(2,7,6)->true
    |x when x=(2,3,2)->true
    |x when x=(6,7,2)->true 
    |_->false
let modnTest n a b c=
    match n with
    |1->true
    |2->mod2Test a b c
    |3->mod3Test a b c
    |4->mod4Test a b c
    |6->(mod2Test a b c) && (mod3Test a b c)
    |8->mod8Test a b c
    |12->(mod4Test a b c) && (mod3Test a b c)
    |24->(mod8Test a b c)&& (mod3Test a b  c)
    |_->false
let poly x  a b c = (pown x 4) + (pown x 3)*a+(pown x 2)*b+x*c
//let polyDivTest x a b c n= 0=(poly x a b c) % n
let xor a b=(a&& not b)||(b&& not a)
(*let modnTestTest n a b c=
    let actualAns=[1..100]|>List.forall(fun x->polyDivTest x a b c n)
    let testAns=modnTest n (int64 a) (int64 b) (int64 c)
    not (xor actualAns  testAns)*)
let fibInc (F1,F2)=(F2,F2+F1)
let inline boolToInt b=
    match b with
    |true->int64 1
    |_->int64 0
//let countIMod24TilM (m:int64)  (i:int64)=
//    match m%(24) with
//    |x when x>=i->1L+m/24- (boolToInt (i=0))
//    |_->m/24-(boolToInt (i=0))


let abcTriplets=
    listMonadBuilder(){
        let!x=[1..24]
        let!y=[1..24]
        let!z=[1..24]
        return x,y,z}
let findMaxDivisor  y=
    let powersOf2 x=Seq.unfold(fun state->match (x|||>modnTest state ) with
                                              |true->Some(state,2*state)
                                              |false->None) 1
                        |>Seq.last
    let test3=match (y|||>modnTest 3)  with
              |true->3
              |false->1
    test3*powersOf2 y
//let a=findMaxDivisor (3,4,5L)
let maxDivisorTriplet=abcTriplets|>List.map(fun x->findMaxDivisor x)
let maxDivisorTripletMap=maxDivisorTriplet|>Seq.zip abcTriplets|>Seq.groupBy(fun (x,y)->y)|>Map.ofSeq|>Map.map(fun key value->Seq.map(fun x->fst x) value)
//let testMap n=maxDivisorTripletMap|>Map.map(fun key value->Seq.filter(fun (a,b,c)->(a<=n) && (b<=n) && (c<=n) && (a > 0L) && (b>0L) && (c>0L))  value)
                                  //|>Map.map(fun key value->Seq.length value)
                                  //|>Map.fold(fun acc key value->acc+key*value) 0
let inline mod10k k x= 
    match x%(pown 10L k) with
    |y when y<0L->y+pown 10L k
    |y->y
let inline BigIntModK k x=
    match x%k with
    |y when y<BigInteger.Zero-> y+k
    |y->y
let inline BigIntMultModK k x y=x*y|>BigIntModK k
let myMultMod10K k (x:int64) y=(x*y)|>mod10k k
let myMult =myMultMod10K 9
let  fastExpGeneric x (n:BigInteger) multFunc =
    let rec fastExpGenericHelp x n acc=match n with
                                            |y when y=0I->acc
                                            |y->match y.IsEven with
                                                |true->fastExpGenericHelp (multFunc x x) (n/2I) acc
                                                |_->fastExpGenericHelp  x (n-1I) (multFunc x acc)
    fastExpGenericHelp x (n-1I) x
type phiForm=
    {
     a:BigRational
     b:BigRational
    }
    static member Zero={a=0N;b=0N}
    static member One={a=1N;b=0N}
    static member (*)(first:phiForm,second:phiForm)=
        {a=(first.a*second.a)+5N*first.b*second.b;b=first.a*second.b+first.b*second.a}
    static member (+)(first:phiForm,second:phiForm)=
        {a=first.a+second.a;b=first.b+second.b}
    static member (-)(first:phiForm,second:phiForm)=
        {a=first.a-second.a;b=first.b-second.b}
    static member complement x={a=x.a;b= -1N*x.b}
    static member (/)(first:phiForm,second:phiForm)=
        let numerator=first*phiForm.complement second
        let denominator=second.a*second.a-5N*second.b*second.b
        {a=numerator.a/denominator;b=numerator.b/denominator}
    static member pown (first:phiForm) (second:BigInteger)=
        match second with
        |y when y=0I->phiForm.One
        |_->fastExpGeneric first second (*)
    static member pownModK (third:BigInteger) (first:phiForm )(second:BigInteger) =
        //Extremely Dangerous function. USE with caution
        let BigRationalModK k (x:BigRational)=( x.Numerator%(k*x.Denominator)|>(fun y->BigRational.FromBigInt y))/BigRational.FromBigInt x.Denominator
        match second with
        |y when y=0I->phiForm.One
        |_->fastExpGeneric first second (fun x y->x*y|>(fun z->{a=BigRationalModK third z.a;b=BigRationalModK third z.b}))
    static member multComplement (x:phiForm)=x*phiForm.complement x|>(fun x->x.a )
    
let phi={a=1N/2N;b=1N/2N}
let psi=phiForm.complement phi
let FibFromPhiModK k n=match n with
                       |y when y=0I->0I
                       |_->((phiForm.pownModK k phi n).b*2N)|>(fun x-> x|>BigRational.ToBigInt|>BigIntModK k)
let fastMatrixExpModK k (M:Matrix<BigInteger>) n=
    let (size,_)=M.Dimensions
    match n with
    |y when y=0I->matrixG.identity size
    |_->fastExpGeneric M n (fun x y->x*y|> (matrixG.map(fun x->BigIntModK k x)))
let fibMatrix=(matrixG.ofSeq[[BigInteger.One;BigInteger.One];[BigInteger.One;BigInteger.Zero]] )
let fastFibModK k n=(fastMatrixExpModK k fibMatrix n).[1,0]
    
let initState1=(0L,1)
let initState2=(0L,1)
let mod109 = mod10k 9
let stateAddK k (q1,r1) (q2,r2) = 
    let remTemp=(r1+r2)
    let rem=match remTemp with
            |x when x>24->((x-24),true)
            |_->(remTemp,false)
    let quotient = (q1+q2+(boolToInt (snd rem)))|>mod10k k
    (quotient,fst rem)
let stateAdd =stateAddK 9
//let dictIModN =
//let countNumTripletsPartial  state=
//    let numRemainderArray=Array.init 24 (fun x->match x with 
//                                                |y when y<=snd state->1L-(boolToInt (int64 y=0L) ) + fst state
//                                                |_->fst state)
//    (fun (x,y,z)-> (numRemainderArray.[x]*numRemainderArray.[ y]) |>mod109|>(fun x ->x*numRemainderArray.[z])|>mod109)
let numRemainderFunc state x= 
        match x with
        |y when y<=snd state->1L+fst state      
        |_->fst state  
let groupByFunc (a,b,c) r=
    let listed=[a;b;c]
    List.fold(fun acc x->
        if x<=r 
        then 
            acc + 1
        else
            acc) 0 listed

let  myPowMod10K k x n  =
    match n with
    |0->1L
    |_->fastExpGeneric x (BigInteger n) (fun x y->x*y|>mod10k  k)
//    let rec myPowMod10KHelp k x n acc= 
//        let y=(mod10k k x)
//        match n with
//        |0->acc
//        |_->match n%2 with
//            |0->myPowMod10KHelp k (myMultMod10K k y y) (n/2) acc
//            |_->myPowMod10KHelp k y (n-1) (myMultMod10K k acc y)
//    myPowMod10KHelp k x n 1L  
let divisorList=[1;2;3;4;6;8;12;24]
let remainderList=[1..24]
let divisorRemainderList=listMonadBuilder() {
                         let!d=divisorList
                         let!r=remainderList
                         return (d,r)}
let createState N=
        let q=N/24I
        let r=N%24I
        match r with
        |y when y=0I->(q-1I,24)
        |_->(q,int r)
let maxDivisorContribRemainderCache=
    let maxDivisorFunc divisor r= 
        maxDivisorTripletMap.[divisor]
        |>Seq.groupBy(fun x->groupByFunc x r)
        |>Seq.map(fun (key,sequence)-> (key,divisor*Seq.length sequence))
        |>Map.ofSeq
    divisorRemainderList
    |>List.map(fun (x,y)->maxDivisorFunc x y)
    |> Seq.zip divisorRemainderList 
    |>Map.ofSeq
    |>Map.map(fun key value->
            Map.fold(fun acc key value->
                let (a,b,c,d)=acc
                match key with
                |3->(int64 value+a,b,c,d)
                |2->(int64 value+a,b-int64 value,c,d)
                |1->(int64 value+a,b-2L*int64 value,c+int64 value,d)
                |_->(int64 value+a,b-3L*int64 value,c+3L*int64 value,d-int64 value)) (0L,0L,0L,0L) value)
let maxDivisorRemainderFunc k (q1,r) d= 
    let q=q1+1L
    maxDivisorContribRemainderCache.[(d,r)]
    |>(fun (a,b,c,d)->(a*(myPowMod10K k q 3 ) )+(b*(myPowMod10K k q 2 ))|>(mod10k k)|> (fun x->x+(c*(myPowMod10K k q 1)))|>(mod10k k)|>(fun x->x+d)|>(mod10k k))

//let countNumTriplets (a,b,c) state= (countNumTripletsPartial state )(a,b,c)
let maxDivisorContribution state d  =
    let numRemainderMap= numRemainderFunc state
    maxDivisorTripletMap.[d]|>Seq.map(fun (a,b,c)->(numRemainderMap a)*numRemainderMap b|>mod109|>(fun x->x*numRemainderMap c)|>mod109)
    |>Seq.fold(fun acc x->mod109 (acc+x)) 0L 
    |>(fun x-> x *int64 d)|>mod109
let findSum2K k y=divisorList|>List.map(fun x->maxDivisorRemainderFunc k y x)|>List.fold(fun acc x->mod10k k (acc+x)) 0L
let findSum3K k y=
        let (q,r)=y
        let qtuple=((myPowMod10K k q 3 ),(myPowMod10K k q 2 ),q,1L)
        List.init (List.length divisorList) (fun x->qtuple)|>List.zip divisorRemainderList|>Map.ofList
let findSum2=findSum2K 9
let fibSum k N=
    let rec fibSumHelp k N state =
        let (prev,prevprev,acc)=state
        match N with
        |1L->acc
        |_->fibSumHelp k (N-1L) ((stateAdd prev prevprev),prev,mod10k k (acc + findSum2K k prev))
    fibSumHelp k N (initState1,initState2,0L)


                                                
let fastFib n=match n with 
              |0L->0I
              |_->(fastExpGeneric  (fibMatrix) (BigInteger n) (*)).[1,0]
let fibSumSkipModK k1 start jump N=
    //The function cannot support large jump values
    let denominator= match jump%2L  with
                     |0L->((fastFib (2L*jump))/(fastFib jump) )-2I
                     |_->(fastFib (2L*jump))/(fastFib jump)
    let jump2=BigInteger jump
    let kNew= denominator*k1
    let secondTerm=fastMatrixExpModK kNew fibMatrix (start+jump2*(N-1I))
    let firstTerm=secondTerm*fastMatrixExpModK kNew fibMatrix jump2|>matrixG.map(fun x->BigIntModK kNew x)
    let thirdTerm=(fastFibModK kNew ((start,jump2)|>BigInteger.Subtract|>BigInteger.Abs) ) 
    let fourthTerm=fastFibModK kNew start
    let thirdTermMultiplier=
        match jump2-start with
        |y when y=0I->0I
        |y when y<0I-> match jump%2L with
                        |0L-> 1I
                        |_-> -1I
        |_-> match start.IsEven with
             |true-> -1I
             |_->1I
    let secondtermMultiplier= match jump%2L with
                              |0L->BigInteger.One
                              |_->BigInteger.MinusOne
    let numerator= (firstTerm.[1,0]-(secondtermMultiplier*secondTerm.[1,0])+thirdTermMultiplier*thirdTerm-fourthTerm)|>BigIntModK kNew
    
    let check=numerator % denominator
    match check with 
    |y when y=0I->BigIntModK k1 (numerator/denominator)
    |_->failwith "something is wrong in fibSumSkipModK"
let fibCubeSecondTermSumSkipModk k start (jump:int64) (N:BigInteger)=
    let isJumpEven=(jump%2L=0L)
    let denominator=
        match isJumpEven with
        |false->phiForm.One+(phiForm.pown phi (BigInteger jump))
        |_->phiForm.One-(phiForm.pown phi (BigInteger jump))
    let kNew=BigInteger.Abs (k*(phiForm.multComplement denominator).Numerator)
    let firstTerm=phiForm.pownModK kNew phi start
    let secondTerm=(start+(BigInteger jump)*N)|>phiForm.pownModK kNew phi
    let numerator=match N.IsEven||isJumpEven with
                  |true->firstTerm-secondTerm
                  |_->firstTerm+secondTerm
    //let minusOne={a= -1N;b=0N}
    let temp=(numerator/denominator).b*2N|>BigRational.ToBigInt
    match (start.IsEven) with
    |true-> temp|>BigIntModK k
    |_-> -1I*temp|>BigIntModK k
let fibSquaredSumSkipModK k start (jump:int64) (N:BigInteger)=
    let jump2=2I*BigInteger jump 
    let denominator=phiForm.pown phi jump2 - phiForm.One
    let kNew=BigInteger.Abs (5I*k*(phiForm.multComplement denominator).Numerator)
    let numerator=phiForm.pownModK kNew phi (2I*start+jump2*N) - phiForm.pownModK kNew phi (2I*start)
    let firstTerm=(numerator/denominator).a*2N|>BigRational.ToBigInt|>BigIntModK (k*5I)
    let constFactorStartContrib=match start.IsEven with 
                                |true-> -1I
                                |_-> 1I
    let constFactor=constFactorStartContrib*
                    match jump%2L=0L with
                    |true->2I*N|>BigIntModK (k*5I)
                    |_->match N.IsEven with 
                        |true->0I
                        |_->2I|>BigIntModK (k*5I)
    (firstTerm+constFactor)/5I|>BigIntModK k
    //let numerator=phiForm.pownModK 
let inline tuplePhiMult x y=
    let a,b=x
    let c,d=y
    ((a*c+5I*b*d),(a*d+b*c))
let fibCubedSumSkipModK k start jump N=
   let firstTerm=fibSumSkipModK (5I*k) (3I*start) (3L*jump) N
   let secondTerm=fibCubeSecondTermSumSkipModk (5I*k) start jump N
   ((firstTerm-3I*secondTerm)/5I)|>BigIntModK k
let quotientCubedSumSkipModK k r start jump N=
    match N with
    |y when y=0I->0I
    |_->let kNew=(pown 24I 3)*k
    
        let firstTerm=fibCubedSumSkipModK kNew start jump N|>BigIntModK kNew
        let secondTerm=(3I*r*r* fibSumSkipModK kNew start jump N)|>BigIntModK kNew
        let thirdTerm=(3I*r*fibSquaredSumSkipModK kNew start jump N)|>BigIntModK kNew
        let lastTerm=r*r*r*N|>BigIntModK kNew
        let result=(firstTerm+secondTerm-(thirdTerm+lastTerm))/(pown 24I 3)|>BigIntModK k
        result
let quotientSquaredSumSkipModK k r start jump N=
    match N with
    |y when y=0I->0I
    |_->let kNew=(pown 24I 2)*k
        let firstTerm=fibSquaredSumSkipModK kNew start jump N|>BigIntModK kNew
        let secondTerm=r*r*N|>BigIntModK kNew
        let thirdTerm=2I*r*(fibSumSkipModK kNew start jump N)|>BigIntModK kNew
        let result=(firstTerm+secondTerm-thirdTerm)/(pown 24I 2)|>BigIntModK k
        result
let quotientSumSkipModK k r start jump N=
    match N with
    |y when y=0I->0I
    |_->let kNew=24I*k
        let result=((fibSumSkipModK kNew start jump N) - (r*N|>BigIntModK kNew))/24I|>BigIntModK k
        result
let findSum4K k N=
    let startList=[2L..25L]
    let remainderList=startList|>List.map(fun x->let z=(fastFib x)%24I
                                                 match z with |y when y=0I->24I|y->y)
    let startRemDict=Map.ofList (List.zip startList remainderList)
    let jump=24L
    let numOfTermList=startList|>List.map(fun x-> match  N%24I with
                                                  |y when y=0I->N/24I
                                                  |_->match (N%24I)>=(-1I+BigInteger x) with
                                                      |true->N/24I+1I
                                                      |_->N/24I)
    let numOfTermStartDict=Map.ofList (List.zip startList numOfTermList)
    let quotientCubedSumDict=numOfTermList
                             |>List.map3(fun (start:int64) remainder numOfTerms->(start,quotientCubedSumSkipModK k (remainder-24I) (BigInteger start) jump numOfTerms)) startList remainderList
                             |>Map.ofList
    let quotientSquaredSumDict=numOfTermList
                               |>List.map3(fun (start:int64) remainder numOfTerms->(start,quotientSquaredSumSkipModK k (remainder-24I)  (BigInteger start) jump numOfTerms)) startList remainderList
                               |>Map.ofList
    let quotientSumDict=numOfTermList
                        |>List.map3(fun (start:int64) remainder numOfTerms->(start,quotientSumSkipModK k (remainder-24I)  (BigInteger start) jump numOfTerms)) startList remainderList
                        |>Map.ofList

    let divStartList=divisorList|>List.map(fun x->startList|>List.map(fun y->(x,y)))|>List.concat

    let result=divStartList
               |>List.map(fun (d,s)->let r=int32 (startRemDict.[s])                                     
                                     maxDivisorContribRemainderCache.[(d,r)]
                                     |>(fun (a,b,c,e)->(BigInteger a)*quotientCubedSumDict.[s] + (BigInteger b)*quotientSquaredSumDict.[s] + (BigInteger c)*quotientSumDict.[s] + (BigInteger e)*numOfTermStartDict.[s]
                                                      |>BigIntModK k))
               |>List.reduce (fun x y->x+y|>BigIntModK k)
    result
//    let multiplier=start+
//    firstTerm+
//let findSum y=divisorList|>List.map(fun x->maxDivisorContribution y x)|>List.fold(fun acc x->mod109 (acc+x)) 0L
