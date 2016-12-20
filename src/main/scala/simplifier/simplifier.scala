package simplifier

import java.lang.Integer

import AST._


// to implement
// avoid one huge match of cases
// take into account non-greedy strategies to resolve cases with power laws
object Simplifier {


  def simplifyIfElse(ifelse: IfElseExpr): Node = {
    //_condition = simplifyEx
    ifelse
  }

  def simplify(node: Node): Node = node match {
    case nodeList @ NodeList(list) => NodeList(simplifyList(list))
    case list @ ElemList(_)  => ElemList(simplifyList(list.list))
    case assignment@Assignment(left, right) => simplifyAssignment(left, right)
    case binExpr@BinExpr(op, left, right) => simplifyBinExpr(binExpr)
    case unary@Unary(_, _) => simplifyUnary(unary)
    case classDef@ClassDef(name, list, suite) => simplifyClassDef(classDef)
    case tuple @ Tuple(_) => simplifyTuple(tuple)
    case intNum @ IntNum(_) => intNum
    case floatNum @ FloatNum(_) => floatNum
    case fundef @ FunDef(_, _, _) => simplifyFundef(fundef)
    case funcall @ FunCall(_, _) => simplifyFuncall(funcall)
    case lambdadef @ LambdaDef(_, _) => simplifyLambda(lambdadef)
    case ifelse @ IfElseExpr (_, _, _) => simplifyIfElse(ifelse)
    case _ => node //NodeList(List(simplifyNode(node).orNull))

  }
  def simplifyAssignment(left: Node, right: Node): Node = {
    val _right = simplify(right)
    if (left != _right) Assignment(left, _right)
    else null
  }

  def simplifyBinExpr(binExpr: BinExpr): Node = {
    val _left = simplify(binExpr.left)
    val _right = simplify(binExpr.right)
//    BinExpr(binExpr.op, _left, _right) match {
//      case binOp@BinExpr("-", IntNum(i), _) => binOp.right
//      case binOp@BinExpr("-", _, IntNum(i)) => binOp.left
//      case binOp@BinExpr("+", IntNum(i), _) => binOp.right
//      case binOp@BinExpr("+", _, IntNum(i)) => binOp.left
//      case binOp@BinExpr("*", IntNum(one), _) => binOp.right
//      case binOp@BinExpr("*", _, IntNum(one)) => binOp.left
//      case binOp@BinExpr("/", IntNum(one), _) => binOp.right
//      case binOp@BinExpr("/", _, IntNum(one)) => binOp.left
//      case binOp@BinExpr("**", num1, num2) =>
    binExpr.op match {
      case "*" =>
        val __left = if (_left.toStr < _right.toStr) _left else _right
        val __right = if (_left.toStr < _right.toStr) _right else _left
        (__left, __right) match {
          case (IntNum(n), _) if n == 0 => IntNum(0)
          case (_, IntNum(n)) if n == 0 => IntNum(0)
          case (IntNum(n), r) if n == 1 => r
          case (l, IntNum(n)) if n == 1 => l
          case (IntNum(l), IntNum(r)) => IntNum(r * l)
          case (l, BinExpr("/", l1, r1)) => simplifyBinExpr(BinExpr("/", simplifyBinExpr(BinExpr("*", l, l1)), r1))
          case (BinExpr("/", l1, r1), r) => simplifyBinExpr(BinExpr("/", simplifyBinExpr(BinExpr("*", r, l1)), r1))
          case (FloatNum(l), FloatNum(r)) => FloatNum(r * l)
          case (BinExpr("**", l1, r1), BinExpr("**", l2, r2)) if l1 == l2 => simplifyBinExpr(BinExpr("**", l1, simplifyBinExpr(BinExpr("+", r1, r2))))
          case (BinExpr("**", l1, r1), r) if l1 == r => simplifyBinExpr(BinExpr("**", l1, simplifyBinExpr(BinExpr("+", r1, IntNum(1)))))
          case (l, BinExpr("**", l1, r1)) if l1 == l => simplifyBinExpr(BinExpr("**", l1, simplifyBinExpr(BinExpr("+", r1, IntNum(1)))))
          case _ => BinExpr(binExpr.op, __left, __right)
        }
      case "+" =>
        (_left, _right) match {
          case (Tuple (l), Tuple (r) ) => Tuple (l ++ r)
          case (ElemList (l), ElemList (r) ) => ElemList (l ++ r)
          case _ => val __left = if (_left.toStr < _right.toStr) _left else _right
            val __right = if (_left.toStr < _right.toStr) _right else _left
            (__left, __right) match {
            case (IntNum (n), r) if n == 0 => r
            case (l, IntNum (n) ) if n == 0 => l
            case (l, Unary ("-", r) ) => simplify (BinExpr ("-", l, r) )
            case (Unary ("-", l), r) => simplify (BinExpr ("-", r, l) )
            case (BinExpr("+",BinExpr("*",BinExpr("*", IntNum(two),l1),r1),BinExpr("**",l2,IntNum(two2))),BinExpr("**",r2,IntNum(two3)))
                if (l1 == l2 && r1 == r2) && (two == two2) && (two2 == two3) && (two3 == 2) =>
              simplifyBinExpr(BinExpr("**", simplifyBinExpr(BinExpr("+", l1, r2)), IntNum(2)))
            case (BinExpr("+",BinExpr("*",BinExpr("*", IntNum(two),l1),r1),BinExpr("**",l2,IntNum(two2))),BinExpr("**",r2,IntNum(two3)))
              if (l2 == r1 && l1 == r2) && (two == two2) && (two2 == two3) && (two3 == 2) =>
              simplifyBinExpr(BinExpr("**", simplifyBinExpr(BinExpr("+", l2, r2)), IntNum(2)))

            case (IntNum (l), IntNum (r) ) => IntNum (r + l)
            case (FloatNum (l), FloatNum (r) ) => FloatNum (r + l)

            case (BinExpr ("*", l1, r1), r) if r1 == r => simplifyBinExpr (BinExpr ("*", simplifyBinExpr (BinExpr ("+", l1, IntNum (1) ) ), r) )
            case (BinExpr ("*", l1, r1), r) if l1 == r => simplifyBinExpr (BinExpr ("*", simplifyBinExpr (BinExpr ("+", r1, IntNum (1) ) ), r) )
            case (l, BinExpr ("*", l1, r1) ) if r1 == l => simplifyBinExpr (BinExpr ("*", simplifyBinExpr (BinExpr ("+", l1, IntNum (1) ) ), l) )
            case (l, BinExpr ("*", l1, r1) ) if l1 == l => simplifyBinExpr (BinExpr ("*", simplifyBinExpr (BinExpr ("+", r1, IntNum (1) ) ), l) )
            case (BinExpr ("*", l1, r1), BinExpr ("*", l2, r2) ) if l1 == l2 => simplifyBinExpr (BinExpr ("*", l1, simplifyBinExpr (BinExpr ("+", r1, r2) ) ) )
            case (BinExpr ("*", l1, r1), BinExpr ("*", l2, r2) ) if l1 == r2 => simplifyBinExpr (BinExpr ("*", l1, simplifyBinExpr (BinExpr ("+", r1, l2) ) ) )
            case (BinExpr ("*", l1, r1), BinExpr ("*", l2, r2) ) if l2 == r1 => simplifyBinExpr (BinExpr ("*", l2, simplifyBinExpr (BinExpr ("+", l1, r2) ) ) )
            case (BinExpr ("*", l1, r1), BinExpr ("*", l2, r2) ) if r1 == r2 => simplifyBinExpr (BinExpr ("*", r1, simplifyBinExpr (BinExpr ("+", l1, l2) ) ) )

            case (BinExpr ("+", IntNum (l1), r1), r) => simplifyBinExpr (BinExpr ("+", IntNum (l1), simplifyBinExpr (BinExpr ("+", r1, r) ) ) )
            case (BinExpr ("-", IntNum (l1), r1), r) => simplifyBinExpr (BinExpr ("-", IntNum (l1), simplifyBinExpr (BinExpr ("+", r1, r) ) ) )
            case (BinExpr ("+", BinExpr ("+", l2, r2), r1), r) => simplifyBinExpr (BinExpr ("+", simplifyBinExpr (BinExpr ("+", l2, r2) ), simplifyBinExpr (BinExpr ("+", r1, r) ) ) )
              //case (BinExpr("+", l1, r1), r) => simplifyBinExpr(BinExpr("+", l1, simplifyBinExpr(BinExpr("+", r1, r))))
            case (BinExpr("+",BinExpr("*",BinExpr("*", IntNum(two),l1),r1),BinExpr("**",l2,IntNum(two2))),BinExpr("**",r2,IntNum(two3)))
                if (l1 == l2 && r1 == r2) && (two == two2) && (two2 == two3) && (two3 == 2) =>
              simplifyBinExpr(BinExpr("**", simplifyBinExpr(BinExpr("+", l1, r2)), IntNum(2)))
            case _ => BinExpr (binExpr.op, __left, __right)
            }
    }
      case "-" => (_left, _right) match {
        case (IntNum(n), r) if n == 0 => r
        case (l, IntNum(n)) if n == 0 => l
        case (IntNum(l), IntNum(r)) => IntNum(l - r)
        case (FloatNum(l), FloatNum(r)) => FloatNum(l - r)
        case (l, r) if l == r => IntNum(0)
    //    case (BinExpr("-", IntNum(l1), r1), r) => simplifyBinExpr(BinExpr("-", IntNum(l1), simplifyBinExpr(BinExpr("-", r1, r))))
    //    case (BinExpr("+", IntNum(l1), r1), r) => simplifyBinExpr(BinExpr("+", IntNum(l1), simplifyBinExpr(BinExpr("-", r1, r))))
        case (BinExpr(op, IntNum(l1), r1), r) if op == "+" || op == "-" =>
            simplifyBinExpr(BinExpr(op, IntNum(l1), simplifyBinExpr(BinExpr("-", r1, r))))
        case (BinExpr("*", l1, r1), r) if r1 == r => simplifyBinExpr(BinExpr("*", simplifyBinExpr(BinExpr("-", l1, IntNum(1))),r))
        case (BinExpr("*", l1, r1), r) if l1 == r => simplifyBinExpr(BinExpr("*", simplifyBinExpr(BinExpr("-", r1, IntNum(1))),r))
        case (l, BinExpr("*", l1, r1)) if r1 == l => simplifyBinExpr(BinExpr("*", simplifyBinExpr(BinExpr("-", l1, IntNum(1))),l))
        case (l, BinExpr("*", l1, r1)) if l1 == l => simplifyBinExpr(BinExpr("*", simplifyBinExpr(BinExpr("-", r1, IntNum(1))),l))
        case (BinExpr("*", l1, r1), BinExpr("*", l2, r2)) if l1 == l2 => simplifyBinExpr(BinExpr("*", l1, simplifyBinExpr(BinExpr("-", r1, r2))))
        case (BinExpr("*", l1, r1), BinExpr("*", l2, r2)) if l1 == r2 => simplifyBinExpr(BinExpr("*", l1, simplifyBinExpr(BinExpr("-", r1, l2))))
        case (BinExpr("*", l1, r1), BinExpr("*", l2, r2)) if l2 == r1 => simplifyBinExpr(BinExpr("*", l2, simplifyBinExpr(BinExpr("-", l1, r2))))
        case (BinExpr("*", l1, r1), BinExpr("*", l2, r2)) if r1 == r2 => simplifyBinExpr(BinExpr("*", r1, simplifyBinExpr(BinExpr("-", l1, l2))))




        case (BinExpr("-",BinExpr("**",BinExpr("+", l1,r1),IntNum(num1)),BinExpr("**",l2,IntNum(num2))), BinExpr("*",BinExpr("*",IntNum(num3),l3),r3))
          if l1 == l3 && r1 == r3 && l1 == l2 && num2 == 2 && num1 == 2 && num3 == 2 => BinExpr("**", r1, IntNum(2))
        case (BinExpr("-",BinExpr("**",BinExpr("+", l1,r1),IntNum(num1)),BinExpr("**",l2,IntNum(num2))), BinExpr("*",BinExpr("*",IntNum(num3),l3),r3))
          if l1 == r3 && l1 == l2 && r1 == l3 && num2 == 2 && num1 == 2 && num3 == 2 => BinExpr("**", r1, IntNum(2))
        case (BinExpr("-",BinExpr("**",BinExpr("+", l1,r1),IntNum(num1)),BinExpr("**",l2,IntNum(num2))), BinExpr("*",BinExpr("*",IntNum(num3),l3),r3))
          if l1 == l3 && r1 == l2 && r1 == r3 && num2 == 2 && num1 == 2 && num3 == 2 => BinExpr("**", l1, IntNum(2))
        case (BinExpr("-",BinExpr("**",BinExpr("+", l1,r1),IntNum(num1)),BinExpr("**",l2,IntNum(num2))), BinExpr("*",BinExpr("*",IntNum(num3),l3),r3))
          if l1 == r3 && r1 ==  l2 && r1 == l3 && num2 == 2 && num1 == 2 && num3 == 2 => BinExpr("**", l1, IntNum(2))
        case _ => BinExpr(binExpr.op, _left, _right)

      }
      case "/" => (_left, _right) match {
        case (IntNum(n), _) if n == 0 => IntNum(0)
        // case (IntNum(n), r) if n == 1 => r
        case (l, r) if l == r => IntNum(1)
        case (l, IntNum(n)) if n == 1 => l
        case (IntNum(l), IntNum(r)) => FloatNum(l / r)
        case (l, BinExpr("/", l1, r1)) => simplifyBinExpr(BinExpr("*", l, simplifyBinExpr(BinExpr("/", r1, l1))))
        case (BinExpr("/", l1, r1), r) => simplifyBinExpr(BinExpr("/", l1, simplifyBinExpr(BinExpr("*", r1, r))))
        case _ => BinExpr(binExpr.op, _left, _right)

      }
      case "**" => (_left, _right) match {
        case (l, null) => l
        case (_, IntNum(k)) if k == 0 => IntNum(1)
        case (l, IntNum(k)) if k == 1 => l
        case (IntNum(l), IntNum(r)) => IntNum(Math.pow(l.toDouble, r.toDouble).toInt)
        case (FloatNum(l), FloatNum(r)) => FloatNum(Math.pow(l.toDouble, r.toDouble))
        case (IntNum(l), FloatNum(r)) => FloatNum(Math.pow(l.toDouble, r.toDouble))
        case (FloatNum(l), IntNum(r)) => FloatNum(Math.pow(l.toDouble, r.toDouble))
        case (BinExpr("**", l1, r1), r) => simplifyBinExpr(BinExpr("**", l1, simplifyBinExpr(BinExpr("*", r1, r))))


        case _ => BinExpr(binExpr.op, _left, _right)
      }
      case "or" =>
        val __left = if (_left.toStr < _right.toStr) _left else _right
        val __right = if (_left.toStr < _right.toStr) _right else _left
        (__left, __right) match {
          case (TrueConst(), _) => TrueConst()
          case (_, TrueConst()) => TrueConst()
          case (FalseConst(), r) => r
          case (l, FalseConst()) => l
          case (l, r) if l == r => l
          case _ => BinExpr("or", __left, __right)
        }
      case "and" =>
        val __left = if (_left.toStr < _right.toStr) _left else _right
        val __right = if (_left.toStr < _right.toStr) _right else _left
        (__left, __right) match {
          case (FalseConst(), _) => FalseConst()
          case (_, FalseConst()) => FalseConst()
          case (TrueConst(), r) => r
          case (l, TrueConst()) => l
          case (l, r) if l == r => l
          case _ => BinExpr("and", __left, __right)
        }
      case ">" =>
        (_left, _right) match {
          case (l, r) if l == r => FalseConst()
          case (IntNum(l), IntNum(r)) if l.intValue() > r.intValue() => TrueConst()
          case (IntNum(l), IntNum(r)) if l.intValue() <= r.intValue() => FalseConst()
          case (FloatNum(l), FloatNum(r)) if l.doubleValue() > r.doubleValue() => TrueConst()
          case (FloatNum(l), IntNum(r)) if l.doubleValue() > r.doubleValue() => TrueConst()
          case (FloatNum(l), FloatNum(r)) if l.doubleValue() <= r.doubleValue() => FalseConst()
          case (FloatNum(l), IntNum(r)) if l.doubleValue() <= r.doubleValue() => FalseConst()
          case (IntNum(l), FloatNum(r)) if l.doubleValue() > r.doubleValue() => TrueConst()
          case (IntNum(l), FloatNum(r)) if l.doubleValue() <= r.doubleValue() => FalseConst()
          case _ => BinExpr(binExpr.op, _left, _right)
        }
      case "<=" =>
        (_left, _right) match {
          case (l, r) if l == r => TrueConst()
          case (IntNum(l), IntNum(r)) if l.intValue() <= r.intValue() => TrueConst()
          case (IntNum(l), IntNum(r)) if l.intValue() > r.intValue() => FalseConst()
          case (FloatNum(l), FloatNum(r)) if l.doubleValue() <= r.doubleValue() => TrueConst()
          case (FloatNum(l), IntNum(r)) if l.doubleValue() <= r.doubleValue() => TrueConst()
          case (FloatNum(l), FloatNum(r)) if l.doubleValue() > r.doubleValue() => FalseConst()
          case (FloatNum(l), IntNum(r)) if l.doubleValue() > r.doubleValue() => FalseConst()
          case (IntNum(l), FloatNum(r)) if l.doubleValue() <= r.doubleValue() => TrueConst()
          case (IntNum(l), FloatNum(r)) if l.doubleValue() > r.doubleValue() => FalseConst()
          case _ => BinExpr(binExpr.op, _left, _right)
        }
      case ">=" =>
        (_left, _right) match {
          case (l, r) if l == r => TrueConst()
          case (IntNum(l), IntNum(r)) if l.intValue() >= r.intValue() => TrueConst()
          case (IntNum(l), IntNum(r)) if l.intValue() < r.intValue() => FalseConst()
          case (FloatNum(l), FloatNum(r)) if l.doubleValue() >= r.doubleValue() => TrueConst()
          case (FloatNum(l), IntNum(r)) if l.doubleValue() >= r.doubleValue() => TrueConst()
          case (FloatNum(l), FloatNum(r)) if l.doubleValue() < r.doubleValue() => FalseConst()
          case (FloatNum(l), IntNum(r)) if l.doubleValue() < r.doubleValue() => FalseConst()
          case (IntNum(l), FloatNum(r)) if l.doubleValue() >= r.doubleValue() => TrueConst()
          case (IntNum(l), FloatNum(r)) if l.doubleValue() < r.doubleValue() => FalseConst()
          case _ => BinExpr(binExpr.op, _left, _right)
        }
      case "<" =>
        (_left, _right) match {
          case (l, r) if l == r => FalseConst()
          case (IntNum(l), IntNum(r)) if l.intValue() < r.intValue() => TrueConst()
          case (IntNum(l), IntNum(r)) if l.intValue() >= r.intValue() => FalseConst()
          case (FloatNum(l), FloatNum(r)) if l.doubleValue() < r.doubleValue() => TrueConst()
          case (FloatNum(l), IntNum(r)) if l.doubleValue() < r.doubleValue() => TrueConst()
          case (FloatNum(l), FloatNum(r)) if l.doubleValue() >= r.doubleValue() => FalseConst()
          case (FloatNum(l), IntNum(r)) if l.doubleValue() >= r.doubleValue() => FalseConst()
          case (IntNum(l), FloatNum(r)) if l.doubleValue() < r.doubleValue() => TrueConst()
          case (IntNum(l), FloatNum(r)) if l.doubleValue() >= r.doubleValue() => FalseConst()
          case _ => BinExpr(binExpr.op, _left, _right)
        }

      case "==" =>
        (_left, _right) match {
          case (l, r) if l == r => TrueConst()
          case (IntNum(l), FloatNum(r)) if l.doubleValue() == r.doubleValue() => TrueConst()
          case (FloatNum(l), IntNum(r)) if l.doubleValue() == r.doubleValue() => TrueConst()
          case (IntNum(l), FloatNum(r)) if l.doubleValue() != r.doubleValue() => FalseConst()
          case (FloatNum(l), IntNum(r)) if l.doubleValue() != r.doubleValue() => FalseConst()
          case (IntNum(l), IntNum(r)) if l.intValue() != r.intValue() => FalseConst()
          case (FloatNum(l), FloatNum(r)) if l.doubleValue() != r.doubleValue() => FalseConst()
          case _ => BinExpr(binExpr.op, _left, _right)
        }
      case "!=" =>
        (_left, _right) match {
          case (l, r) if l == r => FalseConst()
          case (IntNum(l), FloatNum(r)) if l.doubleValue() == r.doubleValue() => FalseConst()
          case (FloatNum(l), IntNum(r)) if l.doubleValue() == r.doubleValue() => FalseConst()
          case (IntNum(l), FloatNum(r)) if l.doubleValue() != r.doubleValue() => TrueConst()
          case (FloatNum(l), IntNum(r)) if l.doubleValue() != r.doubleValue() => TrueConst()
          case (IntNum(l), IntNum(r)) if l.intValue() != r.intValue() => TrueConst()
          case (FloatNum(l), FloatNum(r)) if l.doubleValue() != r.doubleValue() => TrueConst()
          case _ => BinExpr(binExpr.op, _left, _right)
        }

      case _ => BinExpr(binExpr.op, _left, _right)
    }

    //TODO: Inne reguly
    //      op == '-' and l == IntNum(0) => r
    //TODO: Wszystkie operatory
  }

  def simplifyNode (node: Node) : Option[Node] =
    Some(simplify(node))
  def simplifyList(list: List[Node]) = {
    list.flatMap(simplifyNode)
  }
  def simplifyTuple(tuple: Tuple) = Tuple(simplifyList(tuple.list))
  def simplifyClassDef(classDef: ClassDef) = classDef

  def simplifyFundef(fundef: FunDef): Node = {
    FunDef(fundef.name, fundef.formal_args, simplify(fundef.body))
  }
  def simplifyFuncall(funcall: FunCall): Node = {
    FunCall(funcall.name, simplify(funcall.args_list))
  }
  def simplifyLambda(lambdadef: LambdaDef): Node = {
    LambdaDef(lambdadef.formal_args, simplify(lambdadef.body))
  }

  def simplifyUnary(unary: Unary) = {
    val ex = simplify(unary.expr)
    val notMap = Map(
    "==" -> "!=",
      "!=" -> "==",
      "<" -> ">=",
      ">=" -> "<",
      "<=" -> ">",
      ">" -> "<="

      )
    unary.op match{
      case "-" => ex match {
        case (Unary("-", e)) => e
        case IntNum(n) => IntNum(-n)
        case FloatNum(n) => FloatNum(-n)
        case _ => Unary(unary.op,ex)
      }
      case "+" => ex
      case "not" => ex match{
        case TrueConst() => FalseConst()
        case FalseConst() => TrueConst()
        case (BinExpr(op, l, r)) if notMap.contains(op) => simplifyBinExpr(BinExpr(notMap(op), l, r))
        case (Unary("not", e)) => e

        case _ => Unary(unary.op, ex)
      }
      case _ => Unary(unary.op, ex)
    }
  }
}

