

// predicate partitioned(a: array?<int>, i: int)
//   reads a
//   requires a != null
//   {
//     forall k, k' :: 0 <= k <= i < k' < a.Length ==> a[k] <= a[k']
//   }

// method BubbleSort(a: array?<int>)
//   modifies a
//   requires a != null
//   ensures sorted(a, 0, a.Length-1)
//   {
//     var i := a.Length - 1;
//     while(i > 0)
//       invariant i < 0 ==> a.Length == 0
//       invariant sorted(a, i, a.Length-1)
//       invariant partitioned(a, i)
//       {
//         var j := 0;
//         while (j < i)
//           invariant 0 < i < a.Length && 0 <= j <= i
//           invariant sorted(a, i, a.Length-1)
//           invariant partitioned(a, i)
//           invariant forall k :: 0 <= k <= j ==> a[k] <= a[j]
//           {
//             if(a[j] > a[j+1])
//               {
//                 a[j], a[j+1] := a[j+1], a[j];
//               }
//               j := j + 1;
//           }
//           i := i -1;
//       }
//   }

predicate sorted(a: array?<int>, l: int, u: int)
  reads a
  requires a != null
  {
    forall i, j :: 0 <= l <= i <= j <= u < a.Length ==> a[i] <= a[j]
  }


method findMax(a: array?<int>, nr: int) returns(s:int)
    requires a != null
    requires nr != 0
    requires a.Length > 0 
    requires forall  i :: 0<=i<a.Length ==> a[i]>0
    requires a[0]==1
    requires sorted(a, 0, a.Length-1) 
    ensures s>0
{
  var copie := nr;
  s := a[0];
  var i:= 1;
  while (i<a.Length && a[i] <= copie)
    invariant 0 <= i <= a.Length
    invariant s>0
  {
    s := a[i];
    i := i + 1;
  }
}


  method bancnote(a: array?<int>, nr: int)
    requires a != null
    requires nr != 0
    requires a.Length > 0 
    requires forall  i :: 0<=i<a.Length ==> a[i]>0
    requires a[0]==1
    requires sorted(a, 0, a.Length-1)
  {
    var s := 0;
    var copie:=  nr;
    while(copie > 0)
      decreases copie
    {
        var i := 0;
        s := findMax(a,nr);
        print s, "\n";
        copie := copie-s;
    }
  }

  
method Main() {
  var a := new int[7];
  a[0], a[1], a[2], a[3], a[4], a[5], a[6] := 1, 5, 10, 50, 100, 200, 500;
  var nr:= 86;
  bancnote(a,nr);
  // BubbleSort(a);
  // var k := 0;
  // while(k < 5) { print a[k], "\n"; k := k+1;}
}