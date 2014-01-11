module divTest

open System
open System.Numerics
open System.Collections.Generic
type listMonadBuilder()=
        member x.Bind(comp,func)= comp|>List.map(fun x->func x)|> List.concat
        member x.Return(comp)=[comp]
let mod2Test a b c= 0L=((1L+a+b+c) % 2L)
let mod3Test a b c= (2L=b%3L) && (0L=(a+c)%3L)
let mod4Test a b c=
    match a%4L with
    |x when ((x=0L)||(x=2L))->( 0L=( (a+c)%4L) && (3L=b%4L) )   ||( (2L=(a+c)%4L)&&(1L=b%4L) )
    |_->false 
let mod8Test a b c=
    match (a%8L,b%8L,c%8L) with
    |x when x=(6L,3L,6L)->true
    |x when x=(2L,7L,6L)->true
    |x when x=(2L,3L,2L)->true
    |x when x=(6L,7L,2L)->true 
    |_->false
let modnTest n a b c=
    match n with
    |1L->true
    |2L->mod2Test a b c
    |3L->mod3Test a b c
    |4L->mod4Test a b c
    |6L->(mod2Test a b c) && (mod3Test a b c)
    |8L->mod8Test a b c
    |12L->(mod4Test a b c) && (mod3Test a b c)
    |24L->(mod8Test a b c)&& (mod3Test a b  c)
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
//    match m%(24L) with
//    |x when x>=i->1L+m/24L- (boolToInt (i=0L))
//    |_->m/24L-(boolToInt (i=0L))



let abcTriplets=
    listMonadBuilder(){
        let!x=[0L..23L]
        let!y=[0L..23L]
        let!z=[0L..23L]
        return x,y,z}
let findMaxDivisor  y=[|1L;2L;3L;4L;6L;8L;12L;24L|]|>Array.filter(fun x->y|||>modnTest x )|>(fun x->x.[x.Length-1])
let maxDivisorTriplet=abcTriplets|>List.map(fun x->findMaxDivisor x)
let maxDivisorTripletMap=maxDivisorTriplet|>Seq.zip abcTriplets|>Seq.groupBy(fun (x,y)->y)|>Map.ofSeq|>Map.map(fun key value->Seq.map(fun x->fst x) value)
let testMap n=maxDivisorTripletMap|>Map.map(fun key value->Seq.filter(fun (a,b,c)->(a<=n) && (b<=n) && (c<=n) && (a > 0L) && (b>0L) && (c>0L))  value)
                                  //|>Map.map(fun key value->Seq.length value)
                                  //|>Map.fold(fun acc key value->acc+key*value) 0
let inline mod109 x= x%(pown 10L 9)
let initState1=(0L,1L)
let initState2=(0L,1L)
               
let stateAdd (q1,r1) (q2,r2) = 
    let remTemp=(r1+r2)
    let rem=match remTemp with
            |x when x>23L->((x-24L),true)
            |_->(remTemp,false)
    let quotient = (q1+q2+(boolToInt (snd rem)))|>mod109
    (quotient,fst rem)
//let dictIModN =
let countNumTripletsPartial  state=
    let numRemainderMap=[0L..23L]|>List.map(fun x->match x with 
                                                   |y when y<=snd state->(y,1L-(boolToInt (y=0L) ) + fst state)
                                                   |_->(x,fst state))|>Map.ofSeq
    (fun (x,y,z)-> (numRemainderMap.[x]*numRemainderMap.[y]) |>mod109|>(fun x ->x*numRemainderMap.[z])|>mod109)
let countNumTriplets (a,b,c) state= (countNumTripletsPartial state )(a,b,c)
let maxDivisorContribution state d  =
    let numRemainderMap=countNumTripletsPartial state
    maxDivisorTripletMap.[d]|>Seq.map(fun x->numRemainderMap x)
    |>Seq.fold(fun acc x->mod109 (acc+x)) 0L 
    |>(fun x-> x *d)|>mod109

