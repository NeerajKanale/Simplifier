package simplifier


import AST._

// to implement
// avoid one huge match of cases
// take into account non-greedy strategies to resolve cases with power laws
object Simplifier {


  def simplifyIfElse(ifelse: IfElseExpr): Node = {
    val _condition = simplify(ifelse.cond)
    if (_condition == TrueConst()) {
      simplify(ifelse.left)
    } else if (_condition == FalseConst()) {
      simplify(ifelse.right)
    } else
      IfElseExpr(_condition, simplify(ifelse.left), simplify(ifelse.right))
  }


  def simplifyIfElseInstr(ifelse: IfElseInstr): Node = {
    val _condition = simplify(ifelse.cond)
    if (_condition == TrueConst()) {
      simplify(ifelse.left)
    } else if (_condition == FalseConst()) {
      simplify(ifelse.right)
    } else
      IfElseInstr(_condition, simplify(ifelse.left), simplify(ifelse.right))
  }

  def simplifyWhile(whileInstr: WhileInstr): Node = {
    val _condition = simplify(whileInstr.cond)
    if (_condition == FalseConst()) {
      EmptyNode()
    } else WhileInstr(_condition, simplify(whileInstr.body))
  }

  def simplifyDeadAssignment(list: List[Node]): List[Node] = {
    if (list.length < 2) list
    else {
      val simplifiedList = for (index <- 1 to list.length - 1; if ((list(index - 1), list(index)) match {
        case (Assignment(x, y), Assignment(x2, y2)) if x == x2 => false
        case _ => true
      }))
        yield list(index - 1)
      simplifiedList.toList :+ list.last
    }
  }

  def simplifyKeyDatum(list: List[KeyDatum]): Node = {
    var newList = List[KeyDatum]()
    if (list.length < 2) KeyDatumList(list)
    else {
      for (index <- 0 to list.length - 1) {
        var replaced = false
        if (newList.length >= 1) {
          for (i <- 0 to newList.length - 1) {
            if (newList(i).key == list(index).key) {
              newList.updated(i, list(index))
              replaced = true
            }
          }
        }
        if (!replaced)
          newList :+ list(index)
      }
      KeyDatumList(newList)
    }

  }

  def simplify(node: Node): Node = node match {
    case nodeList@NodeList(list) => {
      val simplifiedList = simplifyList(simplifyDeadAssignment(list))
      if (simplifiedList.length == 0) EmptyNode()
      else if (simplifiedList.length == 1) simplifiedList(0)
      else NodeList(simplifiedList)
    }
    case list@ElemList(_) => ElemList(simplifyList(list.list))
    case list@KeyDatumList(_) => simplifyKeyDatum(list.list)
    case assignment@Assignment(left, right) => simplifyAssignment(left, right)
    case binExpr@BinExpr(op, left, right) => simplifyBinExpr(binExpr)
    case unary@Unary(_, _) => simplifyUnary(unary)
    case classDef@ClassDef(name, list, suite) => simplifyClassDef(classDef)
    case tuple@Tuple(_) => simplifyTuple(tuple)
    case intNum@IntNum(_) => intNum
    case floatNum@FloatNum(_) => floatNum
    case fundef@FunDef(_, _, _) => simplifyFundef(fundef)
    case funcall@FunCall(_, _) => simplifyFuncall(funcall)
    case lambdadef@LambdaDef(_, _) => simplifyLambda(lambdadef)
    case ifelse@IfElseExpr(_, _, _) => simplifyIfElse(ifelse)
    case ifelseinstr@IfElseInstr(_, _, _) => simplifyIfElseInstr(ifelseinstr)
    case whileInstr@WhileInstr(_, _) => simplifyWhile(whileInstr)
    case _ => node

  }

  def simplifyAssignment(left: Node, right: Node): Node = {
    val _right = simplify(right)
    if (left != _right) Assignment(left, _right)
    else EmptyNode()
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
          /*          case (MultiargExpr(l, op), BinExpr("+", l1, r1)) => simplifyMultiargExpr(MultiargExpr(l :+ l1 :+ r1, "+"))
                    case (BinExpr("+", l1, r1), BinExpr("*", l2, r2)) =>
                    case (MultiargExpr(l1, "+"), r) => simplifyMultiargExpr(MultiargExpr(l1 ++ List(r), "+"))*/
          case (Tuple(l), Tuple(r)) => simplify(Tuple(l ++ r))
          case (ElemList(l), ElemList(r)) => simplify(ElemList(l ++ r))
          case _ => val __left = if (_left.toStr < _right.toStr) _left else _right
            val __right = if (_left.toStr < _right.toStr) _right else _left
            (__left, __right) match {
              case (IntNum(n), r) if n == 0 => r
              case (l, IntNum(n)) if n == 0 => l
              case (l, Unary("-", r)) => simplify(BinExpr("-", l, r))
              case (Unary("-", l), r) => simplify(BinExpr("-", r, l))
              case (BinExpr("+", BinExpr("*", BinExpr("*", IntNum(two), l1), r1), BinExpr("**", l2, IntNum(two2))), BinExpr("**", r2, IntNum(two3)))
                if (l1 == l2 && r1 == r2) && (two == two2) && (two2 == two3) && (two3 == 2) =>
                simplifyBinExpr(BinExpr("**", simplifyBinExpr(BinExpr("+", l1, r2)), IntNum(2)))
              case (BinExpr("+", BinExpr("*", BinExpr("*", IntNum(two), l1), r1), BinExpr("**", l2, IntNum(two2))), BinExpr("**", r2, IntNum(two3)))
                if (l2 == r1 && l1 == r2) && (two == two2) && (two2 == two3) && (two3 == 2) =>
                simplifyBinExpr(BinExpr("**", simplifyBinExpr(BinExpr("+", l2, r2)), IntNum(2)))

              case (IntNum(l), IntNum(r)) => IntNum(r + l)
              case (FloatNum(l), FloatNum(r)) => FloatNum(r + l)

              //    case (BinExpr("+", BinExpr("+", l3 , BinExpr("+", l4, BinExpr("*")))
              case (BinExpr("+", BinExpr("*", v1, y1), BinExpr("*", x1, BinExpr("+", y2, z1))), BinExpr("*", v2, z2)) if v1 == v2 =>
                //    simplifyBinExpr(BinExpr("*",BinExpr("+",v1,x1),BinExpr("+",y1,z1)))
                simplifyBinExpr(BinExpr("+", BinExpr("*", x1, BinExpr("+", y2, z1)), BinExpr("*", v1, BinExpr("+", y1, z2))))

              case (BinExpr("*", l1, r1), r) if r1 == r => simplifyBinExpr(BinExpr("*", simplifyBinExpr(BinExpr("+", l1, IntNum(1))), r))
              case (BinExpr("*", l1, r1), r) if l1 == r => simplifyBinExpr(BinExpr("*", simplifyBinExpr(BinExpr("+", r1, IntNum(1))), r))
              case (l, BinExpr("*", l1, r1)) if r1 == l => simplifyBinExpr(BinExpr("*", simplifyBinExpr(BinExpr("+", l1, IntNum(1))), l))
              case (l, BinExpr("*", l1, r1)) if l1 == l => simplifyBinExpr(BinExpr("*", simplifyBinExpr(BinExpr("+", r1, IntNum(1))), l))
              case (BinExpr("*", l1, r1), BinExpr("*", l2, r2)) if l1 == l2 => simplifyBinExpr(BinExpr("*", l1, simplifyBinExpr(BinExpr("+", r1, r2))))
              case (BinExpr("*", l1, r1), BinExpr("*", l2, r2)) if l1 == r2 => simplifyBinExpr(BinExpr("*", l1, simplifyBinExpr(BinExpr("+", r1, l2))))
              case (BinExpr("*", l1, r1), BinExpr("*", l2, r2)) if l2 == r1 => simplifyBinExpr(BinExpr("*", l2, simplifyBinExpr(BinExpr("+", l1, r2))))
              case (BinExpr("*", l1, r1), BinExpr("*", l2, r2)) if r1 == r2 => simplifyBinExpr(BinExpr("*", r1, simplifyBinExpr(BinExpr("+", l1, l2))))

              case (BinExpr("+", IntNum(l1), r1), r) => simplifyBinExpr(BinExpr("+", IntNum(l1), simplifyBinExpr(BinExpr("+", r1, r))))
              case (BinExpr("-", IntNum(l1), r1), r) => simplifyBinExpr(BinExpr("-", IntNum(l1), simplifyBinExpr(BinExpr("+", r1, r))))
              case (BinExpr("+", BinExpr("+", l2, r2), r1), r) => simplifyBinExpr(BinExpr("+", simplifyBinExpr(BinExpr("+", l2, r2)), simplifyBinExpr(BinExpr("+", r1, r))))
              //case (BinExpr("+", l1, r1), r) => simplifyBinExpr(BinExpr("+", l1, simplifyBinExpr(BinExpr("+", r1, r))))
              case (BinExpr("+", BinExpr("*", BinExpr("*", IntNum(two), l1), r1), BinExpr("**", l2, IntNum(two2))), BinExpr("**", r2, IntNum(two3)))
                if (l1 == l2 && r1 == r2) && (two == two2) && (two2 == two3) && (two3 == 2) =>
                simplifyBinExpr(BinExpr("**", simplifyBinExpr(BinExpr("+", l1, r2)), IntNum(2)))


              case _ => BinExpr(binExpr.op, __left, __right)
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
        case (BinExpr("*", l1, r1), r) if r1 == r => simplifyBinExpr(BinExpr("*", simplifyBinExpr(BinExpr("-", l1, IntNum(1))), r))
        case (BinExpr("*", l1, r1), r) if l1 == r => simplifyBinExpr(BinExpr("*", simplifyBinExpr(BinExpr("-", r1, IntNum(1))), r))
        case (l, BinExpr("*", l1, r1)) if r1 == l => simplifyBinExpr(BinExpr("*", simplifyBinExpr(BinExpr("-", l1, IntNum(1))), l))
        case (l, BinExpr("*", l1, r1)) if l1 == l => simplifyBinExpr(BinExpr("*", simplifyBinExpr(BinExpr("-", r1, IntNum(1))), l))
        case (BinExpr("*", l1, r1), BinExpr("*", l2, r2)) if l1 == l2 => simplifyBinExpr(BinExpr("*", l1, simplifyBinExpr(BinExpr("-", r1, r2))))
        case (BinExpr("*", l1, r1), BinExpr("*", l2, r2)) if l1 == r2 => simplifyBinExpr(BinExpr("*", l1, simplifyBinExpr(BinExpr("-", r1, l2))))
        case (BinExpr("*", l1, r1), BinExpr("*", l2, r2)) if l2 == r1 => simplifyBinExpr(BinExpr("*", l2, simplifyBinExpr(BinExpr("-", l1, r2))))
        case (BinExpr("*", l1, r1), BinExpr("*", l2, r2)) if r1 == r2 => simplifyBinExpr(BinExpr("*", r1, simplifyBinExpr(BinExpr("-", l1, l2))))


        case (BinExpr("-", BinExpr("**", BinExpr("+", l1, r1), IntNum(num1)), BinExpr("**", l2, IntNum(num2))), BinExpr("*", BinExpr("*", IntNum(num3), l3), r3))
          if l1 == l3 && r1 == r3 && l1 == l2 && num2 == 2 && num1 == 2 && num3 == 2 => BinExpr("**", r1, IntNum(2))
        case (BinExpr("-", BinExpr("**", BinExpr("+", l1, r1), IntNum(num1)), BinExpr("**", l2, IntNum(num2))), BinExpr("*", BinExpr("*", IntNum(num3), l3), r3))
          if l1 == r3 && l1 == l2 && r1 == l3 && num2 == 2 && num1 == 2 && num3 == 2 => BinExpr("**", r1, IntNum(2))
        case (BinExpr("-", BinExpr("**", BinExpr("+", l1, r1), IntNum(num1)), BinExpr("**", l2, IntNum(num2))), BinExpr("*", BinExpr("*", IntNum(num3), l3), r3))
          if l1 == l3 && r1 == l2 && r1 == r3 && num2 == 2 && num1 == 2 && num3 == 2 => BinExpr("**", l1, IntNum(2))
        case (BinExpr("-", BinExpr("**", BinExpr("+", l1, r1), IntNum(num1)), BinExpr("**", l2, IntNum(num2))), BinExpr("*", BinExpr("*", IntNum(num3), l3), r3))
          if l1 == r3 && r1 == l2 && r1 == l3 && num2 == 2 && num1 == 2 && num3 == 2 => BinExpr("**", l1, IntNum(2))

        case (BinExpr("**",BinExpr("+",x1,y1),IntNum(num1)),BinExpr("**",BinExpr("-",x2,y2),IntNum(num2)))
          if x1 == x2 && y1 == y2 && num1 == 2 && num2 == 2 => BinExpr("*",BinExpr("*",IntNum(4),x1),y1)

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
        case (l, null | EmptyNode()) => l
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

  def simplifyNode(node: Node): Option[Node] = {
    Some(simplify(node))
  }


  def simplifyList(list: List[Node]): List[Node] = {
    list.flatMap(simplifyNode).filter(x => x != null && x != EmptyNode())
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
    unary.op match {
      case "-" => ex match {
        case (Unary("-", e)) => e
        case IntNum(n) => IntNum(-n)
        case FloatNum(n) => FloatNum(-n)
        case _ => Unary(unary.op, ex)
      }
      case "+" => ex
      case "not" => ex match {
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

