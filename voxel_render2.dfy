datatype Rectangle = Rectangle(labe: string, x: int, y: int, w:int, h:int, isRoot:bool)

predicate method okRect(r: Rectangle)
{
    r.x >= 0 && r.y >= 0 && r.w >= 1 && r.h >= 1
}

function method absRect(r: Rectangle): seq<int>
{
    [r.x, r.y, r.w, r.h]
}

class Couverture
{
    var rects :array<Rectangle>;
    var roots :array<int>;

    predicate ok()
        reads this, rects
    {
        rects != null &&
        rects.Length > 0
    }

    /*predicate method rectInCover(cover: array<Rectangle>, r: Rectangle)
        reads cover
        requires cover != null
        requires cover.Length > 0
    {
        0 <= r.x
        && 0 <= r.y
    }*/

    predicate method okRects(cover: array<Rectangle>)
        reads cover
        requires cover != null
        requires cover.Length > 0
    {
        forall i :: 0 <= i < cover.Length
        ==> okRect(cover[i])
    }

    /*predicate method rectsInCover(cover: array<Rectangle>)
        reads  cover
        requires cover != null
        requires cover.Length > 0
        requires okRects(cover)
    {
        forall i :: 0 <= i < cover.Length
        ==> rectInCover(cover, cover[i])
    }*/

    predicate method mergeable(a: Rectangle, b: Rectangle)
        requires okRect(a) && okRect(b)
    {
        (a.isRoot && b.isRoot) &&
        (
            (a.x == b.x && a.w == b.w && (a.y+a.h == b.y || b.y+b.h == a.y))
            || (a.y == b.y && a.h == b.h && (a.x+a.w == b.x || b.x+b.w == a.x))
        )
    }

    predicate method optimizedCover(cover :array<Rectangle>)
        reads cover
        requires cover != null && cover.Length > 0
        requires okRects(cover)
    {
        forall i,j :: 0<=i<j<cover.Length
        ==> !mergeable(cover[i],cover[j])
    }

    constructor (r :array<Rectangle>)
        requires r != null
        requires r.Length >= 1
        requires forall k :: 0 <= k < r.Length ==> okRect(r[k]);
        modifies this
        //ensures fresh(rects)
        ensures ok()
        ensures okRects(rects)
    {
        rects := r;
        roots[0] := r.Length;
        /*rects := new Rectangle[r.Length];
        var i := 0;
        while(i<r.Length)
            invariant 0<=i<=r.Length
        {
            rects[i] := r[i];
            i := i+1;
        }*/
    }

    method optimize()
        requires ok()
        requires okRects(rects)
        modifies rects
        modifies roots
        ensures ok()
        ensures okRects(rects)
        ensures optimizedCover(rects)
    {
        var opti := false;
        while(!opti)
            invariant ok()
            invariant okRects(rects)
        {
            opti := improve();
        }
    }

    method canMerge(a: Rectangle, b: Rectangle) returns (ret : bool)
        requires ok()
        requires okRect(a) && okRect(b)
        ensures ok()
        ensures mergeable(a,b) ==> ret == true
        ensures !mergeable(a,b) ==> ret == false
    {
        if(
            (a.isRoot && b.isRoot)
            &&
            (
                (a.x == b.x && a.w == b.w && (a.y+a.h == b.y || b.y+b.h == a.y))
                ||
                (a.y == b.y && a.h == b.h && (a.x+a.w == b.x || b.x+b.w == a.x))
            )
        ){
            ret := true;
        } else {
            ret := false;
        }
    }

    method merge(i :int, j :int) returns (ret :Rectangle)
        requires ok()
        requires okRect(rects[i]) && okRect(rects[j])
        modifies rects
        modifies roots
        ensures ok()
        ensures okRect(ret)
        ensures roots[0] < old(roots[0])
    {
        var a :Rectangle := rects[i];
        var b :Rectangle := rects[j];

        if(a.x <= b.x && a.y <= b.y){
            ret := Rectangle("rect", a.x, a.y, b.x+b.w-a.x, b.y+b.h-a.y, true);
            rects[i] := ret;
            rects[j] := Rectangle("nonRoot", b.x, b.y, b.w, b.h, false);
        } else {
            ret := Rectangle("rect", b.x, b.y, a.x+a.w-b.x, a.y+a.h-b.y, true);
            rects[j] := ret;
            rects[i] := Rectangle("nonRoot", a.x, a.y, a.w, a.h, false);
        }

        roots[0] := roots[0] - 1;
    }

    method improve() returns (optimized: bool)
        requires ok()
        requires okRects(rects)
        modifies rects
        modifies roots
        ensures ok()
        ensures okRects(rects)
        ensures 0<=roots[0]<=old(roots[0])
    {
        var i := 0;
        var j := i+1;
        var rect1 :Rectangle := rects[i];
        var rect2 :Rectangle;
        var cm := false;

        while(!cm && i<rects.Length)
            invariant ok()
            invariant okRects(rects)
            invariant 0<=i<=rects.Length
            invariant 0<=j<=rects.Length
        {
            j := i+1;
            rect2 := rects[j];
            while(!cm && j<rects.Length)
                invariant ok()
                invariant okRects(rects)
                invariant 0<=i<=rects.Length
                invariant 0<=j<=rects.Length
            {
                j := j+1;
                rect2 := rects[j];
                cm := canMerge(rect1, rect2);
            }
            if(!cm){
                i := i+1;
                rect1 := rects[i];
            }
        }

        if(cm){
            optimized := false;
            var rectTmp : Rectangle := merge(i,j);
        } else {
            optimized := true;
        }
    }

    /*
    * Affiche une Couverture dans le terminal
    */
    method toString(r: Rectangle)
    {
        print r.x, ",", r.y, ",", r.w, ",", r.h, ",", r.labe, ",", r.isRoot;
    }

    method dump()
        requires ok()
        ensures ok()
    {
        print "\n";
        var y := 0;
        while (y < rects.Length)
            invariant 0 <= y <= rects.Length
        {
            toString(rects[y]);
            print "\n";
            y := y + 1;
        }
    }
}


method Test(c: Couverture, g: array<Rectangle>)
    requires g != null
    requires g.Length > 0
    requires c != null
    requires c.ok()
    modifies c
    modifies c.rects
    modifies c.roots
    ensures c.ok()
{
    c.optimize();
}

method Main()
{
    /* Test 1 a 2x2 not optimized */
    var g := new Rectangle[4];
    g[0] := Rectangle("one",0,0,1,1,true);
    g[1] := Rectangle("two",0,1,1,1,true);
    g[2] := Rectangle("three",1,0,1,1,true);
    g[3] := Rectangle("four",1,1,1,1,true);
    var c := new Couverture(g);
    Test(c,g);
    print "\n";
    // c.dump();

    // Couverture de 2x2
    var t1 := new Rectangle[4];
    t1[0] := Rectangle("one",0,0,1,1,true);
    t1[1] := Rectangle("two",1,0,1,1,true);
    t1[2] := Rectangle("tree",0,1,1,1,true);
    t1[3] := Rectangle("four",1,1,1,1,true);
    var couv1 :Couverture;
    couv1 := new Couverture(t1);
    Test(couv1,t1);
    print "\n";
    // couv1.dump();

    //Couverture de 3x3 avec un trou en bas à droite
    var t2 := new Rectangle[8];
    t2[0] := Rectangle("one",0,0,1,1,true);
    t2[1] := Rectangle("two",1,0,1,1,true);
    t2[2] := Rectangle("tree",2,0,1,1,true);
    t2[3] := Rectangle("four",0,1,1,1,true);
    t2[4] := Rectangle("five",1,1,1,1,true);
    t2[5] := Rectangle("six",2,1,1,1,true);
    t2[6] := Rectangle("seven",0,2,1,1,true);
    t2[7] := Rectangle("eight",1,2,1,1,true);
    var couv2 :Couverture;
    couv2 := new Couverture(t2);
    Test(couv2,t2);
    print "\n";
    // couv2.dump();

    //Couverture de 2x2 avec deux trous déjà optimisée
    var t3 := new Rectangle[2];
    t3[0] := Rectangle("one",0,0,1,1,true);
    t3[1] := Rectangle("four",1,1,1,1,true);
    var couv3 :Couverture;
    couv3 := new Couverture(t3);
    Test(couv3,t3);
    // couv3.dump();
}
