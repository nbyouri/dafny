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
    var rects :array2<Rectangle>;

    predicate ok()
        reads this, rects
    {
        rects != null &&
        rects.Length0 > 0 &&
        rects.Length1 > 0
    }

    predicate ok_bis()
        requires ok()
        reads this, rects
    {
        forall i,j :: 0 <= i < rects.Length0 && 0 <= j < rects.Length1
          ==> okRect(rects[i,j])
    }

    predicate method rectInCover(cover: array2<Rectangle>, r: Rectangle)
        reads cover
        requires cover != null
        requires cover.Length0 > 0
        requires cover.Length1 > 0
    {
        0 <= r.x < cover.Length0 &&
        0 <= r.y < cover.Length1
        // 0 <= (x + rects[x,y].w) < rects.Length0 &&
        // 0 <= (y + rects[x,y].h) < rects.Length1
    }

    predicate method okRects(cover: array2<Rectangle>)
        reads cover
        requires cover != null
        requires cover.Length0 > 0
        requires cover.Length1 > 0
    {
        forall i,j :: 0 <= i < cover.Length0 && 0 <= j < cover.Length1
          ==> okRect(cover[i,j])
    }

    predicate method rectsInCover(cover: array2<Rectangle>)
        reads  cover
        requires cover != null
        requires cover.Length0 > 0
        requires cover.Length1 > 0
        requires okRects(cover)
    {
        forall i,j :: 0 <= i < cover.Length0 && 0 <= j < cover.Length1
          ==> rectInCover(cover, cover[i,j])
    }

    /*
    predicate method cannotMergeH(cover: array2<Rectangle>)
        reads cover
        requires cover != null
        requires cover.Length0 > 0
        requires cover.Length1 > 0
        requires okRects(cover)
        requires rectsInCover(cover)
    {
        forall y,ki,kj :: (0<=y<cover.Length1) && (0<=ki<kj<cover.Length0) && (cover[ki,y].isRoot) && (cover[kj,y].isRoot) && cover[ki,y].h == cover[kj,y].h
        ==> !(cover[ki,y].x+cover[ki,y].w == cover[kj,y].x)
    }

    predicate method cannotMergeV(cover: array2<Rectangle>)
        reads cover
        requires cover != null
        requires cover.Length0 > 0
        requires cover.Length1 > 0
        requires okRects(cover)
        requires rectsInCover(cover)
    {
        forall x,ki,kj :: (0<=x<cover.Length0) && (0<=ki<kj<cover.Length1) && (cover[x,ki].isRoot) && (cover[x,kj].isRoot) && cover[x,ki].w == cover[x,kj].w
        ==> !(cover[x,ki].y+cover[x,ki].h == cover[x,kj].y)
    }*/

    predicate method optimizedCover(cover :array2<Rectangle>)
        reads cover
        requires cover != null
        requires cover.Length0 > 0
        requires cover.Length1 > 0
        requires okRects(cover)
        requires rectsInCover(cover)
    {
        forall i1, i2 , j1, j2
        :: 0<=i1<cover.Length0
        && 0<=i2<cover.Length0
        && 0<=j1<cover.Length1
        && 0<=j2<cover.Length1
        && cover[i1,j1].isRoot
        && cover[i2,j2].isRoot
        && !(i1==i2 && j1==j2)
        ==>
        cover[i1,j1].x+cover[i1,j1].w == cover[i2,j2].x
        || cover[i2,j2].x+cover[i2,j2].w == cover[i1,j1].x
        || cover[i1,j1].y+cover[i1,j1].h == cover[i2,j2].y
        || cover[i2,j2].y+cover[i2,j2].h == cover[i1,j1].y
    }

    /* Le constructeur de la classe Couverture prend un array de Rectangle en
     * paramètre et initialise la Couverture en trois étapes :
     * - Définir les limites en hauteur et largeur de la Couverture en inspectant
     *   les coordonnées des Rectangles en entrée;
     * - Initialiser la Couverture, une array2 aux tailles mesurées précédemment
     *   et la remplir de Rectangles "vides" de taille unitaire;
     * - Remplir cette Couverture avec les Rectangles passés en paramètre.
     * On initialise aussi le booléen :
     */
    constructor (r: array<Rectangle>)
        requires r != null
        requires r.Length >= 1
        requires forall k :: 0 <= k < r.Length ==> okRect(r[k]);
        modifies this
        ensures fresh(rects)
        ensures ok()
        ensures okRects(rects)
        ensures rectsInCover(rects)
    {
        //On trouve les dimensions x et y nécessaires pour notre Couverture
        var size_x,size_y := 1,1;
        var i := 0;
        while (i < r.Length)
            invariant ((0 <= i <= r.Length) && (forall k :int :: k>=0 &&
            k<i ==> (r[k].x+r[k].w <= size_x) && (r[k].y+r[k].h <= size_y)) &&
            (size_x>=1 && size_y>=1)); // TODO simplify
        {
            if (r[i].x + r[i].w > size_x) {
                size_x := r[i].x + r[i].w;
            }
            if (r[i].y + r[i].h > size_y) {
                size_y := r[i].y + r[i].h;
            }
            i := i + 1;
        }

        //On initialise un array2<Rectangle> considérée "vide"
        var trects := new Rectangle[size_x,size_y];
        assert(size_x>=1 && size_y>=1 && trects != null && trects.Length0>=1 && trects.Length1>=1);
        var j := 0;
        i := 0;
        while (i < size_x)
            invariant 0 <= i <= size_x;
            invariant forall kx, ky :: 0 <= kx < i && 0 <= ky < size_y ==> okRect(trects[kx,ky]) && rectInCover(trects,trects[kx,ky]);
        {
            j := 0;
            while (j < size_y)
                invariant 0 <= j <= size_y;
                invariant forall kx :int, ky :int :: 0 <= kx < i && 0 <= ky < size_y ==> okRect(trects[kx,ky]) && rectInCover(trects,trects[kx,ky]);
                invariant forall ky :int :: 0 <= ky < j ==> okRect(trects[i,ky]) && rectInCover(trects,trects[i,ky]);
            {
                trects[i,j] := Rectangle("placeholder",i,j,1,1,false);
                assert okRect(trects[i,j]); // ok
                assert rectInCover(trects, trects[i,j]);
                j := j + 1;
            }
            i := i + 1;
        }
        i := 0;
        assert okRects(trects) && rectsInCover(trects);

        //On remplit le array2 avec les Rectangle passés en paramètre
        while (i < r.Length)
            invariant 0 <= i <= r.Length;
            invariant okRects(trects) && rectsInCover(trects);
        {
            trects[r[i].x,r[i].y] := r[i];
            assert okRect(trects[r[i].x,r[i].y]); // ok
            assert rectInCover(trects, trects[r[i].x,r[i].y]);
            i := i + 1;
        }
        assert okRects(trects) && rectsInCover(trects);

        // wtf
        /*i := 0;
        while (i < size_x)
            invariant 0 <= i <= size_x;
        {
            j := 0;
            while (j < size_y)
                invariant 0 <= i <= size_x;
                invariant 0 <= j <= size_y;
            {
                var r := trects[i,j];
                var ok := okRect(r);
                var ic := rectInCover(trects, r);
                toString(r);
                print ",",ok,",",ic; // show trues yet is assert violation??
                print "\n";
                assert rectInCover(trects, trects[i,j]);
                // assert okRect(r) && rectInCover(trects, r); // assert violation wtf
                j := j + 1;
            }
            i := i + 1;
        }*/

        rects := trects;
        assert okRects(rects) && rectsInCover(rects);
    }

    /*
     * Le fonctionnement d'optimize est relativement simple, en fonction de la
     * direction déterminée par horizImprove, il va lancer improve en boucle dans
     * une direction, jusqu'à ce que la Couverture soit optimsée dans cette direction,
     * puis il fera la même chose dans l'autre direction, s'assurant ainsi que la
     * surface est optimisée localement.
     */
    method optimize()
        requires ok()
        //requires ok_bis()
        requires okRects(rects)
        requires rectsInCover(rects)
        modifies this
        modifies rects
        ensures ok()
        ensures okRects(rects)
        ensures rectsInCover(rects)
        ensures optimizedCover(rects)
    {
        //On choisit la première direction d'opti
        var horizImprove:bool;
	      if (rects.Length0 >= rects.Length1) {
            horizImprove := true;
        } else {
            horizImprove := false;
        }

        var hack := rects.Length0 * rects.Length1;
        var opti := false;
        while(!opti && hack > 0)
        {
            opti := improve(horizImprove);
            hack := hack - 1;
        }
    }

    /*
     * canMerge vérifie si deux Rectangles peuvent être fusionnés, en comparant
     * leurs positions et leurs dimensions
     */
    method canMerge(a: Rectangle, b: Rectangle) returns (ret : bool)
        requires ok()
        requires okRect(a) && okRect(b)
        requires rectInCover(rects,a) && rectInCover(rects,b)
        ensures ok()
    {
        //Cas horizontal
        var hMerge := a.x + a.w == b.x && a.h == b.h && a.y == b.y;
        // Cas vertical
        var vMerge := a.x == b.x && a.w == b.w && a.y + a.h == b.y;
        if (hMerge || vMerge) {
            ret := true;
        } else {
            //Cas horizontal
            hMerge := b.x + b.w == a.x && b.h == a.h && b.y == a.y;
            // Cas vertical
            vMerge := b.x == a.x && b.w == a.w && b.y + b.h == a.y;
            if (hMerge || vMerge) {
                ret := true;
            } else {
                ret := false;
            }
        }
    }

    /*
     * merge est utilisé après un canMerge réussi et fusionne deux Rectangles d'une
     * même Couverture : la variable de classe contenant la couverture sera modifiée
     * et le Rectangle résultant de la fusion sera retourné.
     * La fusion ne s'opère qu'entre deux Rectangles "root", après la fusion le
     * Rectangle englobé par l'autre n'est plus considéré comme root, et le
     * principal voit ses dimensions agrandies.
     */
    method merge(a: Rectangle, b: Rectangle, horizImprove:bool) returns (ret : Rectangle)
        requires ok()
        requires okRect(a) && okRect(b)
        requires rectInCover(rects,a) && rectInCover(rects,b)
        modifies rects
        ensures ok()
        ensures okRect(ret)
        ensures rectInCover(rects,ret)
    {
        if (a.x < rects.Length0 && b.x < rects.Length0 &&
            a.y < rects.Length1 && b.y < rects.Length1 &&
            0 <= a.x && 0 <= a.y && 0 <= b.x && 0 <= b.y) {
            if (horizImprove) {
                if (a.x < b.x) {
                    rects[a.x,a.y] := Rectangle(a.labe,a.x,a.y,a.w + b.w,a.h,true);
                    rects[b.x,b.y] := Rectangle(b.labe,b.x,b.y,b.w,b.h,false);
                    ret := rects[a.x,a.y];
                } else {
                    rects[b.x,b.y] := Rectangle(b.labe,b.x,b.y,a.w + b.w,b.h,true);
                    rects[a.x,a.y] := Rectangle(a.labe,a.x,a.y,a.w,a.h,false);
                    ret := rects[b.x,b.y];
                }
            } else {
                if (a.y < b.y){
                    rects[b.x,b.y] := Rectangle(b.labe,b.x,b.y,b.w,b.h,false);
                    rects[a.x,a.y] := Rectangle(a.labe,a.x,a.y,a.w,a.h+b.h,true);
                    ret := rects[a.x,a.y];
                } else {
                    rects[b.x,b.y] := Rectangle(b.labe,b.x,b.y,a.w,b.h+a.h,true);
                    rects[a.x,a.y] := Rectangle(a.labe,a.x,a.y,a.w,a.h,false);
                    ret := rects[b.x,b.y];
                }
            }
        }
    }

    /*
     * L'implémentation actuelle de improve fusionne deux Rectangles deux Rectangles
     * d'une Couverture en un seul (voir merge). Pour trouver deux rectangles valides
     * (root) on utilise nextRectangle, si canMerge indique qu'une fusion est possible,
     * alors on utilise merge pour les fusionner, sinon on passe à la paire de Rectangles
     * suivante. Si l'on a parcouru toute la Couverture sans trouver de paire pouvant
     * être fusionnées, cela veut dire que la Couverture est optimisée dans cette
     * direction
     */
    method improve(horizImprove:bool) returns (optimized: bool)
        requires ok()
        //requires ok_bis()
        requires okRects(rects)
        requires rectsInCover(rects)
        modifies rects
        ensures ok()
        ensures okRects(rects)
        ensures rectsInCover(rects)
    {
        //init
        var i,j := 0,0;
        var rect1 :Rectangle;
        if (rects[i,j].isRoot) {
            rect1 := rects[i,j];
        } else {
            rect1 := nextRectangle(rects[i,j], horizImprove);
        }
        var rect2 :Rectangle;
        var cm :bool := false;

        //Pour chaque rect1
        var hack1 := rects.Length0*rects.Length1;
        while (!cm && rect1.isRoot && hack1 > 0)
        {
            rect2 := nextRectangle(rect1, horizImprove);
            //Pour chaque rect2 après rect1
            var hack2 := rects.Length0*rects.Length1;
            while (!cm && rect2.isRoot && hack2 > 0)
            {
                rect2 := nextRectangle(rect2, horizImprove);
                cm := canMerge(rect1,rect2);
                hack2 := hack2 - 1;
            }
            if(!cm){
                rect1 := nextRectangle(rect1, horizImprove);
            }
            hack1 := hack1 - 1;
        }

        //we found a canMerge ORELSE the couv is already optimized
        if (cm) {
            var rect3 := merge(rect1, rect2, horizImprove);
            optimized := false;
        } else {
            optimized := true;
        }
    }

    /*
    * À partir d'un Rectangle, nextRectangle trouve le prochain Rectangle valide de
    * la Couverture, dans la direction horizontale ou verticale selon horizImprove
    */
    method nextRectangle(r: Rectangle, horizImprove: bool) returns (ret:Rectangle)
        requires ok()
        // requires ok_bis()
        requires okRect(r)
        requires rectInCover(rects, r)
        requires okRects(rects)
        requires rectsInCover(rects)
        ensures ok()
        ensures okRect(ret)
        ensures rectInCover(rects, ret)
        ensures okRects(rects)
        ensures rectsInCover(rects)
    {
        //Cas de base, parcours horizontal
        if (horizImprove) {
            var rec_temp:Rectangle := Rectangle("endOfCouv",0,0,1,1,false);
            ret := rec_temp;

            var ix := r.x + 1;
            var iy := r.y;
            var found := false;
            while (iy < rects.Length1 && !found)
                invariant 0 <= iy <= rects.Length1;
                invariant 0 <= ix <= rects.Length0;
                invariant okRects(rects) && rectsInCover(rects);
                invariant okRect(ret) && rectInCover(rects, ret);
            {
                while (ix < rects.Length0 && !found)
                    invariant 0 <= ix <= rects.Length0;
                    invariant okRects(rects) && rectsInCover(rects);
                    invariant okRect(ret) && rectInCover(rects, ret);
                {
                    if (rects[ix,iy].isRoot) {
                        found := true;
                        //NV// assert okRect(rects[ix,iy]);
                        ret := rects[ix,iy];
                    }
                    ix := ix + 1;
                }
                ix := 0;
                iy := iy + 1;
            }
            /*if (!found) {
                var rec_temp:Rectangle := Rectangle("endOfCouv",0,0,1,1,false);
                assert okRect(rec_temp);
                assert rectInCover(rects, rec_temp);
                ret := rec_temp;
                assert okRect(ret);
                assert rectInCover(rects, ret);
            }*/
        } else {
            var rec_temp:Rectangle := Rectangle("endOfCouv",0,0,1,1,false);
            ret := rec_temp;

            var ix := r.x;
            var iy := r.y+1;
            var found := false;
            while (ix < rects.Length0 && !found)
                invariant 0 <= iy <= rects.Length1;
                invariant 0 <= ix <= rects.Length0;
                invariant okRects(rects) && rectsInCover(rects);
                invariant okRect(ret) && rectInCover(rects, ret);
            {
                while (iy < rects.Length1 && !found)
                    invariant 0 <= iy <= rects.Length1;
                    invariant okRects(rects) && rectsInCover(rects);
                    invariant okRect(ret) && rectInCover(rects, ret);
                {
                    if (rects[ix,iy].isRoot) {
                        found := true;
                        // NV//assert okRect(rects[ix,iy]);
                        ret := rects[ix,iy];
                    }
                    iy := iy + 1;
                }
                iy := 0;
                ix := ix + 1;
            }
            /*if (!found) {
                var rec_temp:Rectangle := Rectangle("endOfCouv",0,0,1,1,false);
                assert okRect(rec_temp);
                assert rectInCover(rects, rec_temp);
                ret := rec_temp;
            }*/
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
        while (y < rects.Length1)
            invariant 0 <= y <= rects.Length1
        {
            var x := 0;
            while (x < rects.Length0)
                invariant 0 <= x <= rects.Length0
            {
                toString(rects[x,y]);
                x := x + 1;
            }
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
