#ifndef __EXPR_BV__HH_
#define __EXPR_BV__HH_

/** Bit-Vector expressions 
    
 * This file is included from middle of Expr.hpp
 */
namespace expr
{
  namespace op
  {
    namespace bv
    {
      struct BvSort
      {
        unsigned m_width;
        BvSort (unsigned width) : m_width (width) {}
        BvSort (const BvSort &o) : m_width (o.m_width) {}
        
 	bool operator< (const BvSort &b) const { return m_width < b.m_width; }
	bool operator== (const BvSort &b) const { return m_width == b.m_width; }
	bool operator!= (const BvSort &b) const { return m_width != b.m_width; }
	
	size_t hash () const
	{
	  std::hash<unsigned> hasher;
	  return hasher (m_width);
	}
	
	void Print (std::ostream &OS) const { OS << "bv(" << m_width << ")"; }	
      };
      inline std::ostream &operator<< (std::ostream &OS, const BvSort &b)
      {
	b.Print (OS);
	return OS;
      }       
    }
  }
  
  template<> struct TerminalTrait<const op::bv::BvSort>
  {
    typedef const op::bv::BvSort value_type;
    
    static inline void print (std::ostream &OS, 
			      const op::bv::BvSort &b, 
			      int depth, bool brkt) { OS << b; }
    static inline bool less (const op::bv::BvSort &b1, 
			     const op::bv::BvSort &b2)
    { return b1 < b2; }
	
    static inline bool equal_to (const op::bv::BvSort &b1, 
				 const op::bv::BvSort &b2)
    { return b1 == b2; }
	
    static inline size_t hash (const op::bv::BvSort &b) 
    { return b.hash (); }
  };
  
  namespace op
  {
    typedef Terminal<const bv::BvSort> BVSORT;
    
    namespace bv
    {
      inline Expr bvsort (unsigned width, ExprFactory &efac)
      {return mkTerm<const BvSort> (BvSort (width), efac);}
      
      inline unsigned width (Expr bvsort)
      {return getTerm<const BvSort>(bvsort).m_width;}
      
      /// Bit-vector numeral of a given sort
      /// num is an integer numeral, and bvsort is a bit-vector sort
      inline Expr bvnum (Expr num, Expr bvsort)
      {return bind::bind (num, bvsort);}
      
      /// bit-vector numeral of an arbitrary precision integer
      inline Expr bvnum (mpz_class num, unsigned bwidth, ExprFactory &efac)
      {return bvnum (mkTerm (num, efac), bvsort (bwidth, efac));}
      
      /// true if v is a bit-vector numeral
      inline bool is_bvnum (Expr v)
      {
        return isOpX<BIND> (v) && v->arity () == 2 &&
          isOpX<MPZ> (v->arg (0)) && isOpX<BVSORT> (v->arg (1));
      }

      inline mpz_class toMpz (Expr v)
      {
        assert (is_bvnum (v));
        return getTerm<mpz_class> (v->arg (0));
      }


      inline Expr bvConst (Expr v, unsigned width)
      {
        Expr sort = bvsort (width, v->efac ());
        return bind::mkConst (v, sort);
      }
      
      
    }
    
    NOP_BASE(BvOp)
    NOP(BNOT,"bvnot",FUNCTIONAL,BvOp)
    NOP(BREDAND,"bvredand",FUNCTIONAL,BvOp)
    NOP(BREDOR,"bvredor",FUNCTIONAL,BvOp)
    NOP(BAND,"bvand",FUNCTIONAL,BvOp)
    NOP(BOR,"bvor",FUNCTIONAL,BvOp)
    NOP(BXOR,"bvxor",FUNCTIONAL,BvOp)
    NOP(BNAND,"bvnand",FUNCTIONAL,BvOp)
    NOP(BNOR,"bvnor",FUNCTIONAL,BvOp)
    NOP(BXNOR,"bvxnor",FUNCTIONAL,BvOp)
    NOP(BNEG,"bvneg",FUNCTIONAL,BvOp)
    NOP(BADD,"bvadd",FUNCTIONAL,BvOp)
    NOP(BSUB,"bvsub",FUNCTIONAL,BvOp)
    NOP(BMUL,"bvmul",FUNCTIONAL,BvOp)
    NOP(BUDIV,"bvudiv",FUNCTIONAL,BvOp)
    NOP(BSDIV,"bvsdiv",FUNCTIONAL,BvOp)
    NOP(BUREM,"bvurem",FUNCTIONAL,BvOp)
    NOP(BSREM,"bvsrem",FUNCTIONAL,BvOp)
    NOP(BSMOD,"bvsmod",FUNCTIONAL,BvOp)
    NOP(BULT,"bvult",FUNCTIONAL,BvOp)
    NOP(BSLT,"bvslt",FUNCTIONAL,BvOp)
    NOP(BULE,"bvule",FUNCTIONAL,BvOp)
    NOP(BSLE,"bvsle",FUNCTIONAL,BvOp)
    NOP(BUGE,"bvuge",FUNCTIONAL,BvOp)
    NOP(BSGE,"bvsge",FUNCTIONAL,BvOp)
    NOP(BUGT,"bvugt",FUNCTIONAL,BvOp)
    NOP(BSGT,"bvsgt",FUNCTIONAL,BvOp)
    NOP(BCONCAT,"concat",FUNCTIONAL,BvOp)
    NOP(BEXTRACT,"extract",FUNCTIONAL,BvOp)
    NOP(BSEXT,"bvsext",FUNCTIONAL,BvOp)
    NOP(BZEXT,"bvzext",FUNCTIONAL,BvOp)
    NOP(BREPEAT,"bvrepeat",FUNCTIONAL,BvOp)
    NOP(BSHL,"bvshl",FUNCTIONAL,BvOp)
    NOP(BLSHR,"bvlshr",FUNCTIONAL,BvOp)
    NOP(BASHR,"bvashr",FUNCTIONAL,BvOp)
    NOP(BROTATE_LEFT,"bvrotleft",FUNCTIONAL,BvOp)
    NOP(BROTATE_RIGHT,"bvrotright",FUNCTIONAL,BvOp)
    NOP(BEXT_ROTATE_LEFT,"bvextrotleft",FUNCTIONAL,BvOp)
    NOP(BEXT_ROTATE_RIGHT,"bvextrotright",FUNCTIONAL,BvOp)
    NOP(INT2BV,"int2bv",FUNCTIONAL,BvOp)
    NOP(BV2INT,"bv2int",FUNCTIONAL,BvOp)
    
    namespace bv
    {
      /* XXX Add helper methods as needed */

      inline Expr bvnot (Expr v) {return mk<BNOT> (v);}
      
      inline Expr extract (unsigned high, unsigned low, Expr v)
      {
        assert (high > low);
        return mk<BEXTRACT> (mkTerm<unsigned> (high, v->efac ()), 
                             mkTerm<unsigned> (low, v->efac ()), v);
      }
      
      /// high bit to extract
      inline unsigned high (Expr v) {return getTerm<unsigned> (v->arg (0));}
      /// low bit to extract
      inline unsigned low (Expr v) {return getTerm<unsigned> (v->arg (1));}
      /// bv argument to extract
      inline Expr earg (Expr v) {return v->arg (2);}
      
      inline Expr sext (Expr v, unsigned width)
      {return mk<BSEXT> (v, bvsort (width, v->efac ()));}
      
      inline Expr zext (Expr v, unsigned width) 
      {return mk<BZEXT> (v, bvsort (width, v->efac ()));}
      
    }
    
  }
}


#endif /*  __EXPR_BV__HH_ */
