package io.github.tgeng.stalker.core

enum CaseTree {
  case CTerm(tm: Term)
  case CLam(body: CaseTree)
  case CRecord(fields: List[FieldValue])
  case CDataCase(idx: Int, branches: List[CaseBranch])
  case CIdCase(idx: Int, τ: Substitution[Term], body: CaseTree)
}

case class FieldValue(name: String, body: CaseTree)
case class CaseBranch(name: String, body: CaseTree)