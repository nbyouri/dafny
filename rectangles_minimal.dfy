
    datatype Point = P(x: int, y: int)

    datatype Rectangle = R(x: int, y: int, w: int, h: int)

    predicate method ok(q: Rectangle)
    { 0 <= q.x < q.x + q.w && 0 <= q.y < q.y + q.h && 0 < q.w && 0 < q.h }

    predicate method contains(q: Rectangle, p: Point)
    { q.x <= p.x < q.x + q.w && q.y <= p.y < q.y + q.h }

    function method abs(q: Rectangle): set<Point>
    { set x, y | q.x <= x < q.x + q.w && q.y <= y < q.y + q.h :: Point.P(x, y) }

    predicate method canMerge(a: Rectangle, b: Rectangle)
    { 
        (a.h == b.h && a.y == b.y && ((a.x + a.w == b.x) || (b.x + b.w == a.x)))
        || (a.w == b.w && a.x == b.x && ((a.y + a.h == b.y) || (b.y + b.h == a.y)))
    }

    function method merge(a: Rectangle, b: Rectangle): Rectangle
    { 
           if a.h == b.h && a.y == b.y && a.x + a.w == b.x then R(a.x, a.y, a.w + b.w, a.h)
      else if a.h == b.h && a.y == b.y && b.x + b.w == a.x then R(b.x, b.y, a.w + b.w, b.h)
      else if a.w == b.w && a.x == b.x && a.y + a.h == b.y then R(a.x, a.y, a.w, a.h + b.h)
      else /* a.w == b.w && a.x == b.x && b.y + b.h == a.y */   R(b.x, b.y, b.w, a.h + b.h)
    }


    class Couverture {
    
        var rectangles: array<Rectangle>;
        var size: int;

        constructor (qs: array<Rectangle>)
            modifies this
            requires qs != null;
            ensures rectangles == qs && size == qs.Length
            ensures valid()
        {
            rectangles, size := qs, qs.Length;
        }

        predicate valid() 
            reads this, rectangles
        {
            rectangles != null && 0 <= size <= rectangles.Length
        }

        method mergeTwo(i: int, j: int)
            requires valid()
            requires 0 <= i < j < size
            modifies rectangles, this
            ensures rectangles == old(rectangles)
            ensures 0 <= size == old(size) - 1 < old(size)
        {
            rectangles[i] := merge(rectangles[i], rectangles[j]);
            if (j < size - 1) {
                rectangles[j] := rectangles[size-1];
            }
            size := size - 1;
        }

        method tryMerge()
            requires valid()
            modifies rectangles, this
            ensures rectangles == old(rectangles)
            ensures valid()
            ensures size <= old(size)
        {
                var i := 0;
                while i < size
                    invariant 0 <= i <= size <= old(size)
                    invariant rectangles == old(rectangles)
                    decreases rectangles.Length - i
                {
                    ghost var i' := i;
                    var j := size - 1;
                    while j > i
                        invariant 0 <= i < size <= old(size)
                        invariant i <= j < size <= old(size)
                        invariant rectangles == old(rectangles)
                    {
                        if canMerge(rectangles[i], rectangles[j]) {
                            mergeTwo(i, j);
                        }
                        j := j - 1;
                    }
                    assert i == i';
                    i := i + 1;
                }
        }

        method simplify()
            requires valid()
            modifies this, rectangles
            ensures rectangles == old(rectangles)
            ensures 0 <= size <= old(size)
            ensures valid()
        {
            var s := size;
            var decreased := true;
            while decreased
                invariant rectangles == old(rectangles)
                invariant valid()
                invariant old(size) >= s >= size >= 0
                decreases decreased, size
            {
                var s := size;
                tryMerge();
                decreased := s > size;
            }
        }

        method dump() 
            requires valid()
        {
            var i := 0;
            var first := true;
            print "[ ";
            while i < size
            {
                if !first { print ", "; }
                print rectangles[i];
                i := i + 1;
                first := false;
            }
            print " ]\n";
        }
    }

method Main() 
{
    var g := new Rectangle[3];
    g[0], g[1], g[2] := R(0,0,1,1), R(1,0,1,1), R(0,1,1,1);

    var m := new Couverture(g);
    m.dump();
    m.simplify();
    m.dump();
}

