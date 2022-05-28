predicate isSol(sol : seq<int>, nr:int)
   requires |sol| == 3
   requires sol[0]>=0
   requires sol[1]>=0
   requires sol[2]>=0
{
    sol[0]*1+sol[1]*5+sol[2]*10 == nr

}

function cost(sol : seq<int>):int 
   requires |sol| == 3
   requires sol[0]>=0
   requires sol[1]>=0
   requires sol[2]>=0
{
    sol[0]+sol[1]+sol[2]
}

predicate isOptSol(sol : seq<int>, nr:int)
    requires |sol| == 3
    requires sol[0]>=0
    requires sol[1]>=0
    requires sol[2]>=0
{   
  isSol(sol,nr) &&
  forall sol' :: |sol'| == 3 && sol'[0]>=0 && sol'[1]>=0 && sol'[2]>=0 && isSol(sol',nr) ==> cost(sol') >= cost(sol)

}

predicate INV(copie: int, nr: int, s1: int, s5: int, s10:int)
  requires s1 >= 0
  requires s5 >= 0
  requires s10 >= 0
{
   forall s1', s5', s10' :: s1'>=0 && s5'>=0 && s10'>=0 
          && isOptSol([s1',s5',s10'],copie) ==> 
          isOptSol([s1+s1',s5+s5',s10+s10'],nr)
}


method findMax(nr: int) returns(s:int)
  requires nr>0
    ensures 0<s <= nr
    ensures s == 1 || s==5 || s==10
    ensures s==1 ==> nr< 5
  
{
  var a := new int[3];
  a[0], a[1], a[2] := 1, 5, 10;
  s := a[0];
  var i:= 1;
  //3 if 
  while (i<a.Length && a[i] <= nr)
    invariant 0 <= i <= a.Length
    invariant 0<s<=nr
    invariant s == 1 || s==5 || s==10
  {
    s := a[i];
    i := i + 1;
  }
}


lemma caz1(copie: int, nr: int, s1: int, s5: int, s10: int)
  requires copie < 5
  requires s1 >= 0
  requires s5 >= 0
  requires s10 >= 0
  requires INV(copie,nr,s1,s5,s10)
  ensures INV(copie-1,nr,s1+1,s5,s10)
{
  assume false;
}

lemma caz2(copie: int,nr: int,s1: int,s5: int,s10: int)
  requires copie >= 5
  requires s1 >= 0
  requires s5 >= 0
  requires s10 >= 0
  requires INV(copie,nr,s1,s5,s10)
  ensures INV(copie-5,nr,s1,s5+1,s10)
{
  assume false;
}

lemma caz3(copie: int,nr: int,s1: int,s5: int,s10: int)
  requires copie >= 10
  requires s1 >= 0
  requires s5 >= 0
  requires s10 >= 0
  requires INV(copie,nr,s1,s5,s10)
  ensures INV(copie-10,nr,s1,s5,s10+1)
{
  assume false;
}


  method bancnote(nr: int) returns (sol: seq<int>)
    requires nr>=0
    ensures |sol| == 3
    ensures sol[0]>=0
    ensures sol[1]>=0
    ensures sol[2]>=0
    ensures isSol(sol,nr)
    ensures isOptSol(sol,nr)
{
    var copie:=  nr;
    var s1 := 0;
    var s5 := 0;
    var s10 := 0;
    while(copie > 0)
      decreases copie
      invariant 0<=copie<=nr
      invariant isSol([s1,s5,s10],nr-copie)
      invariant INV(copie,nr,s1,s5,s10)
    {
        var i := 0;
        var s := findMax(copie);
        if( s == 1){
          caz1(copie,nr,s1,s5,s10);
            s1:=s1+1;
            assert isSol([s1,s5,s10],nr-(copie-1));
            assert INV(copie-1,nr,s1,s5,s10);
        }
        else{
            if(s == 5)
            {
                s5:=s5+1;
                assert isSol([s1,s5,s10],nr-(copie-5));
              
                assert INV(copie-5,nr,s1,s5,s10);

            }
            else{
                s10:=s10+1;
                assert isSol([s1,s5,s10],nr-(copie-10));
                assert INV(copie-10,nr,s1,s5,s10);

            }
        }
        copie := copie-s;
    }
    sol := [s1,s5,s10];

  }

  
method Main() {
  var nr:= 38;
  var sol:=bancnote(nr);
  print sol;
}