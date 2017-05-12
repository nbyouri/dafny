
    datatype Rectangle = Rectangle(x :int, y :int, w :int, h :int)

    predicate method ok(q :Rectangle)
    { 0 <= q.x < q.x + q.w && 0 <= q.y < q.y + q.h && 0 < q.w && 0 < q.h }

    function method subMerge(a :Rectangle, b :Rectangle) :Rectangle
    {
           if a.h == b.h && a.y == b.y && a.x + a.w == b.x then Rectangle(a.x, a.y, a.w + b.w, a.h)
      else if a.h == b.h && a.y == b.y && b.x + b.w == a.x then Rectangle(b.x, b.y, a.w + b.w, b.h)
      else if a.w == b.w && a.x == b.x && a.y + a.h == b.y then Rectangle(a.x, a.y, a.w, a.h + b.h)
      else /* a.w == b.w && a.x == b.x && b.y + b.h == a.y */   Rectangle(b.x, b.y, b.w, a.h + b.h)
    }

    class Couverture {

        var rects :array<Rectangle>;
        var roots :int;

        predicate ok()
            reads this, rects
        {
            rects != null
            && rects.Length > 0
            && 0 <= roots <= rects.Length
        }

        predicate method optimizedCover(cover :array<Rectangle>)
            reads cover
            requires cover != null && cover.Length > 0
        {
            forall i,j :: 0<=i<j<cover.Length
            ==> !canMerge(cover[i],cover[j])
        }

        constructor (r :array<Rectangle>)
            modifies this
            requires r != null && r.Length>0
            ensures rects == r && roots == r.Length
            ensures ok()
        {
            rects, roots := r, r.Length;
        }

        method optimize()
            requires ok()
            modifies this, rects
            ensures rects == old(rects)
            ensures 0 <= roots <= old(roots)
            ensures ok()
            ensures optimizedCover(rects)
        {
            var s := roots;
            var decreased := true;
            while decreased
                invariant rects == old(rects)
                invariant ok()
                invariant old(roots) >= s >= roots >= 0
                decreases decreased, roots
            {
                var s := roots;
                improve();
                decreased := s > roots;
            }
        }

        predicate method canMerge(a :Rectangle, b :Rectangle)
        {
            (a.h == b.h && a.y == b.y && ((a.x + a.w == b.x) || (b.x + b.w == a.x)))
            || (a.w == b.w && a.x == b.x && ((a.y + a.h == b.y) || (b.y + b.h == a.y)))
        }

        method merge(i :int, j :int)
            requires ok()
            requires 0 <= i < j < roots
            modifies rects, this
            ensures rects == old(rects)
            ensures 0 <= roots == old(roots) - 1 < old(roots)
        {
            rects[i] := subMerge(rects[i], rects[j]);
            if (j < roots - 1) {
                rects[j] := rects[roots-1];
            }
            roots := roots - 1;
        }

        method improve()
            requires ok()
            modifies rects, this
            ensures rects == old(rects)
            ensures ok()
            ensures roots <= old(roots)
        {
                var i := 0;
                while i < roots
                    invariant 0 <= i <= roots <= old(roots)
                    invariant rects == old(rects)
                    decreases rects.Length - i
                {
                    ghost var i' := i;
                    var j := roots - 1;
                    while j > i
                        invariant 0 <= i < roots <= old(roots)
                        invariant i <= j < roots <= old(roots)
                        invariant rects == old(rects)
                    {
                        if canMerge(rects[i], rects[j]) {
                            merge(i, j);
                        }
                        j := j - 1;
                    }
                    assert i == i';
                    i := i + 1;
                }
        }

        method toString(r :Rectangle)
        {
            print r.x, ",", r.y, ",", r.w, ",", r.h;
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

    method Test(c :Couverture, g :array<Rectangle>)
        requires g != null
        requires g.Length > 0
        requires c != null
        requires c.ok()
        modifies c
        modifies c.rects
        ensures c.ok()
    {
        c.optimize();
    }

    method Main()
    {
        /* Test 1 a 2x2 not optimized */
        var g := new Rectangle[4];
        g[0] := Rectangle(0,0,1,1);
        g[1] := Rectangle(0,1,1,1);
        g[2] := Rectangle(1,0,1,1);
        g[3] := Rectangle(1,1,1,1);
        var c := new Couverture(g);
        Test(c,g);
        print "\n";
        // c.dump();

    }
