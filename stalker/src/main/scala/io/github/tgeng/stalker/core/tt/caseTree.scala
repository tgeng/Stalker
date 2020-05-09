package io.github.tgeng.stalker.core.tt

enum CaseTree extends Raisable[CaseTree] with Substitutable[Term, CaseTree]{
  case CTerm(tm: Term)
  case CLam(body: CaseTree)
  case CRecord(fields: Map[String, CaseTree])
  case CDataCase(idx: Int, branches: Map[String, CaseTree])
  case CIdCase(idx: Int, restoringSubst: Substitution[Term], body: CaseTree)

  def raiseImpl(using spec: RaiseSpec) : CaseTree = this match {
    case CTerm(tm) => CTerm(tm.raiseImpl)
    case CLam(body) => CLam(body.raiseImpl)
    case CRecord(fields) => CRecord(fields.transform((k, v) => v.raiseImpl))
    case CDataCase(idx, branches) => CDataCase(spec.trans(idx), branches.transform((k, v) => v.raiseImpl))
    case CIdCase(idx, restoringSubst, body) => CIdCase(spec.trans(idx), restoringSubst.map(_.raiseImpl), body.raiseImpl)
  }

  def substituteImpl(using spec: SubstituteSpec[Term]) : CaseTree = this match {
    case CTerm(tm) => CTerm(tm.substituteImpl)
    case CLam(body) => CLam(body.substituteImpl)
    case CRecord(fields) => CRecord(fields.transform((k, v) => v.substituteImpl))
    case CDataCase(idx, branches) => spec.trans(idx) match {
      case Right(_) => throw IllegalStateException()
      case Left(idx) => CDataCase(idx, branches.transform((k, v) => v.substituteImpl))
    }
    case CIdCase(idx, restoringSubst, body) => spec.trans(idx) match {
      case Right(_) => throw IllegalStateException()
      case Left(idx) => CIdCase(idx, restoringSubst.map(_.substituteImpl), body.substituteImpl)
    }
  }
}
