

trait Env {

  type ValueMap = Map[String, ValueDeclBody]
  type TypeMap  = Map[String, TypeDeclBody]

  val body : Map[String, (ValueMap, TypeMap)]

  def +(x : String, decls : List[Declaration]) = {
    val mapPair : (ValueMap, TypeMap) = {
      val init : (ValueMap, TypeMap) = (Map(), Map());
      decls.foldLeft(init){ case ((valmap, tymap), decl) =>
        decl match {
          case DeclForValueLabel(vl, vd) => (valmap + ((vl, vd)), tymap)
          case DeclForTypeLabel(tl, td)  => (valmap, tymap + ((tl, td)))
        }
      }
    };
    new Env { val body = Env.this.body + ((x, mapPair)) }
  }


  def findValueDecl(x : String, vlabel : String) : Option[ValueDeclBody] =
    body.get(x) flatMap { case (valmap, _) =>
      valmap.get(vlabel)
    }

}

class EmptyEnv extends Env {
  val body : Map[String, (ValueMap, TypeMap)] = Map()
}


sealed trait EvalError
case class NotImplementedYet(msg : String)            extends EvalError
case class ValueLabelNotFound(vl : String)            extends EvalError
case class FieldNotEmbodied(vl : String)              extends EvalError
case class MethodNotImplemented(vl : String)          extends EvalError
case class NotAFieldButAMethod(vl : String)           extends EvalError
case class NotAMethodButAField(vl : String)           extends EvalError
case class WrongNumberOfArguments(le : Int, la : Int) extends EvalError

class FWSInterpreter {

  def run(ast : Ast) = {
    val env = new EmptyEnv;
    interpret(env, ast)
  }


  def interpret(env : Env, ast : Ast) : Either[EvalError, Value] =
    ast match {
      case ValNewIn(x, ty, ast0) =>
        lookupDeclarations(env, ty, x) flatMap { case decls =>
          interpret(env + (x, decls), ast0)
        }

      case Var(x) =>
        Right(ValVar(x))

      case Access(ast0, vlabel) =>
        interpret(env, ast0) flatMap { case ValVar(x) =>
          env.findValueDecl(x, vlabel) match {
            case None                            => Left(ValueLabelNotFound(vlabel))
            case Some(DeclDef(_, _, _))          => Left(NotAFieldButAMethod(vlabel))
            case Some(DeclVal(_, None))          => Left(FieldNotEmbodied(vlabel))
            case Some(DeclVal(ty, Some(astNew))) => interpret(env, astNew)
          }
        }

      case Call(ast0, vlabel, astargs) =>
        interpret(env, ast0) flatMap { case ValVar(x) =>
          (env.findValueDecl(x, vlabel) match {
            case None                                    => Left(ValueLabelNotFound(vlabel))
            case Some(DeclVal(_, _))                     => Left(NotAFieldButAMethod(vlabel))
            case Some(DeclDef(_, _, None))               => Left(MethodNotImplemented(vlabel))
            case Some(DeclDef(params, ty, Some(astImp))) => Right((params, ty, astImp))
          }) flatMap { case (params, ty, astImp) =>
            val resInit : Either[EvalError, List[Value]] = Right(Nil);
            astargs.foldLeft(resInit){ case (res, astarg) =>
              res flatMap { case vacc =>
                interpret(env, astarg) flatMap { case varg =>
                  Right(varg :: vacc)
                }
              }
            } flatMap { case vargsrev : List[Value] =>
              val vargs = vargsrev.reverse;
              substituteParams(vargs, params, astImp) flatMap { case astNew =>
                interpret(env, astNew)
              }
            }
          }
        }
/*
        Left(NotImplementedYet("evaluation for method calls"))  // TEMPORARY
*/
    }


  val substituteParams : (List[Value], List[(String, Type)], Ast) => Either[EvalError, Ast] =
    (vargs, params, astImp) => {
      val lenActual = vargs.length;
      val lenExpected = params.length;
      if (lenActual != lenExpected) {
        Left(WrongNumberOfArguments(lenExpected, lenActual))
      } else {
        val lst : List[(Value, (String, Type))] = vargs.zip(params);
        val astImpNew : Ast = {
          lst.foldLeft(astImp){ case (astImp, (varg, (x, _))) =>
            substitute(varg, x, astImp)
          }
        };
        Right(astImpNew)
      }
    }


  val substitute : (Value, String, Ast) => Ast =
    (varg, x, astMain) => {
      astMain // TEMPORARY; should implement the substitution of variable occurences
    }

  def lookupDeclarations(env : Env, ty : Type, x : String) : Either[EvalError, List[Declaration]] =
    Right(Nil)  // TEMPORARY
}
