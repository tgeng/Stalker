package io.github.tgeng.stalker.core

enum CaseTree {
  case CTerm(tm: Term)
  case CLam(body: CaseTree)
  case CRecord(fields: Map[String, CaseTree])
  case CDataCase(idx: Int, branches: Map[String, CaseTree])
  case CIdCase(idx: Int, τ: Substitution[Term], body: CaseTree)
}
