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
    requires isSol(sol,nr)
{   

  forall sol' :: |sol'| == 3 && sol'[0]>=0 && sol'[1]>=0 && sol'[2]>=0 && isSol(sol',nr) ==> cost(sol') >= cost(sol)

}



method findMax(nr: int) returns(s:int)
    requires nr != 0
    ensures s>0
{
  var a := new int[3];
  a[0], a[1], a[2] := 1, 5, 10;
  s := a[0];
  var i:= 1;
  //3 if 
  while (i<a.Length && a[i] <= nr)
    invariant 0 <= i <= a.Length
    invariant s>0
  {
    s := a[i];
    i := i + 1;
  }
}


  method bancnote(nr: int) returns (sol: seq<int>)
    requires nr != 0
    ensures |sol| == 3
    requires sol[0]>=0
    requires sol[1]>=0
    requires sol[2]>=0
    ensures isOptSol(sol,nr)
  {
    var copie:=  nr;
    var s1 := 0;
    var s5 := 0;
    var s10 := 0;
    while(copie > 0)
      decreases copie
    {
        var i := 0;
        var s := findMax(copie);
        if( s == 1){
            s1:=s1+1;
        }
        else{
            if(s == 5)
            {
                s5:=s5+1;
            }
            else{
                s10:=s10+1;
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