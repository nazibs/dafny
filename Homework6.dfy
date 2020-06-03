datatype Tree<T> = Leaf | Node(Tree<T>, Tree<T>, T)
datatype List<T> = Nil | Cons(T, List<T>)

function flatten<T>(tree:Tree<T>):List<T>
{
	match tree
    case Leaf => Nil
    // case Node(left, right, ele) => append(flatten(left), append(flatten(right), Cons(ele, Nil)))
    case Node(left, right, ele) => append(flatten(left), append(Cons(ele, Nil), flatten(right)))
}


function append<T>(xs:List<T>, ys:List<T>):List<T>
ensures xs == Nil ==> append(xs, ys) == ys
ensures ys == Nil ==> append(xs, ys) == xs
ensures length(append(xs,ys)) == length(xs) + length(ys)
{
    match xs
    case Nil => ys
    case Cons(x,xs') => Cons(x, append(xs',ys))
}


function length<T>(xs:List<T>) : int
{
    match xs
    case Nil => 0
    case Cons(x,xs') => 1 + length(xs')
}


function treeContains<T>(tree:Tree<T>, element:T):bool
{
	match tree
    // case Leaf => (Leaf == element) || false
    case Leaf => false
    case Node(left, right, val) => treeContains(left, element) || treeContains(right, element) || (val == element)
}


function listContains<T>(xs:List<T>, element:T):bool
{
	match xs
    case Nil => false
    case Cons(x, xs') => (x==element) || listContains(xs', element)
}   


ghost method listContains_Exp<T>(xs:List<T>, ys:List<T>, element:T)
ensures listContains(append(xs, ys), element) ==  (listContains(xs, element) || listContains(ys, element))
{
    match(xs)
    case Nil => { }
    case Cons(x,xs') => {
        calc {
            listContains(append(xs, ys), element) ;

            == listContains(Cons(x, append(xs', ys)), element) ;

            == listContains(xs, element) || listContains(ys, element) ;
        } 
    }
}


lemma sameElements<T>(tree:Tree<T>, element:T)
ensures treeContains(tree, element) <==> listContains(flatten(tree), element)
{   
    match(tree)
    case Leaf => {}
    case Node(left, right, ele) => {
        calc { treeContains(tree, element) ;

            == treeContains(Node(left, right, ele), element) ;
        
            == treeContains(left, element) || treeContains(right, element) || (ele == element) ;
        
            == listContains(flatten(left), element) || listContains(flatten(right), element) || (ele == element) ;

            == listContains(flatten(left), element) || listContains(Cons(ele, flatten(right)), element) ;

            == listContains(flatten(left), element) || listContains(append(Cons(ele, flatten(right)), Nil), element) ;

            == listContains(flatten(left), element) || listContains(append(Cons(ele, Nil), flatten(right)), element) ;
            
            == {listContains_Exp(flatten(left), append(Cons(ele, Nil), flatten(right)), element);}
                listContains(append(flatten(left), append(Cons(ele, Nil), flatten(right))), element) ;

            == listContains(flatten(tree), element) ;
        }
    }
}