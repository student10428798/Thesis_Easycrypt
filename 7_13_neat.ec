require import Real Bool DBool.
require import Int.

type key.
type plaintext.
type ciphertext.
  (* Encrypt and decrypt operations *)
op [lossless]keygen: key distr.
op [lossless]msggen: plaintext distr.
op enc: key -> plaintext -> ciphertext.
op dec: key ->ciphertext ->plaintext.
(* Compute operations for the adversary *)
op comp: ciphertext -> bool.

module Lsigma_cpaL    = {
  var k:key
  proc k_init() : key ={
  k <$ keygen;
    return(k);
  }
  proc eavesdrop(m1:plaintext, m2:plaintext) : ciphertext = {
      var c:ciphertext;
      c <- enc k m1;
      return(c);
  }
  }.

  module Lsigma_cpaR    = {
  var k:key
  proc k_init() : key ={
  k <$ keygen;
    return(k);
  }
      proc eavesdrop(m1:plaintext, m2:plaintext) : ciphertext = {
      var c:ciphertext;
  c <- enc k m2;
  return(c);
    }
  }.

 module Lsigmaleft    = {
  var k:key
  proc k_init() : key ={
  k <$ keygen;
    return(k);
  }
      proc challenge(m1:plaintext) : ciphertext = {
      var c:ciphertext;

  c <- enc k m1;
  return(c);
    }
  }.

  module Lsigmaright    = {
  var k:key
  proc k_init() : key ={
  k <$ keygen;
    return(k);
  }
      proc challenge(m1:plaintext) : ciphertext = {
      var c:ciphertext;
      var m2:plaintext;
      m2 <$ msggen;
      c <- enc k m2;
      return(c);
    }
  }.


     module Lsigmaleft_Lsigma_cpaLHybrid ={
    proc challenge(m1:plaintext) : ciphertext = {
     var c:ciphertext;
     var m2:plaintext;
     m2 <$ msggen;
    c <@ Lsigma_cpaL.eavesdrop(m1,m2);
      return(c);
      }
    }.

    module Lsigmaright_Lsigma_cpaRHybrid ={
      proc challenge(m1:plaintext) : ciphertext ={
      var c: ciphertext;
      var m2:plaintext;
      m2 <$ msggen;
      c<@ Lsigma_cpaR.eavesdrop(m1,m2);
      return(c);
        }
      }.

  
  module Lsigmaleft_eavesdropL = {
        proc eavesdrop(m1:plaintext, m2:plaintext) : ciphertext ={
        var c: ciphertext;
        c <@ Lsigmaleft.challenge(m1);
        return(c);
      }
    }.

      module Lsigmaleft_eavesdropR = {
        proc eavesdrop(m1:plaintext, m2:plaintext) : ciphertext ={
        var c: ciphertext;
        c <@ Lsigmaleft.challenge(m2);
        return(c);
      }
    }.

    module Lsigmaright_eavesdropL = {
      proc eavesdrop(m1:plaintext, m2:plaintext) : ciphertext ={
       var c: ciphertext;
       c <@ Lsigmaright.challenge(m1);
       return(c);
      }
    }.

    module Lsigmaright_eavesdropR = {
      proc eavesdrop(m1:plaintext, m2:plaintext) : ciphertext ={
       var c: ciphertext;
       c <@ Lsigmaright.challenge(m2);
       return(c);
      }
    }.






lemma Lsigmaleft_equiv_Lsigmaright_if_cpa_secure:
equiv [Lsigma_cpaL.eavesdrop~Lsigma_cpaR.eavesdrop :  ={arg} /\ Lsigma_cpaL.k{1} = Lsigma_cpaR.k{2} ==> ={res} ]  =>   equiv[Lsigmaleft.challenge~Lsigmaright.challenge: ={arg} /\ Lsigmaleft.k{1} = Lsigmaright.k{2} ==> ={res} ].
    proof.
      progress.
    (*transitivity from Lsigmaleft.challenge to Lsigmaleft_cpaLHybrid.challenge*)
      transitivity Lsigmaleft_Lsigma_cpaLHybrid.challenge
    (={arg} /\ Lsigmaleft.k{1}=Lsigma_cpaL.k{2} ==> ={res})
    (={arg} /\Lsigma_cpaL.k{1} = Lsigmaright.k{2}==> ={res}).
      progress.
      exists Lsigmaright.k{2}.
      exists arg{2}.
      auto.
      auto.
      proc.
      inline*.
      wp.
      rnd{2}.
      skip.
      progress.

      (*transitivity from Lsigmaleft_Lsigma_cpaLHybrid.challenge to Lsigmaright_Lsigma_cpaRHybrid.challenge*)
      transitivity Lsigmaright_Lsigma_cpaRHybrid.challenge
      (={arg} /\ Lsigma_cpaL.k{1} = Lsigma_cpaR.k{2}==> ={res})
      (={arg} /\ Lsigma_cpaR.k{1} = Lsigmaright.k{2} ==> ={res}).
      progress.
      exists Lsigmaright.k{2}.
      exists arg{2}.
      auto.
      auto.
      proc.
     call H.
      rnd.
      progress.

      (*transitivity from Lsigmaright_Lsigma_cpaRHybrid.challenge to Lsigmaright.challenge*)
      transitivity Lsigmaright.challenge
    (={arg} /\ Lsigma_cpaR.k{1} = Lsigmaright.k{2} ==> ={res})
    (={arg} /\ Lsigmaright.k{1} = Lsigmaright.k{2} ==> ={res}).
      progress.
    exists Lsigmaright.k{2}.
      exists arg{2}.
    progress.
      auto.
      proc.
      inline*.
      wp.
      rnd.
      skip.
      auto.

    (*prove lsigmaright = lsigmaright with different k.*)
    
      proc.
    auto.
  qed.





lemma Lsigma_cpaL_equiv_Lsigma_cpaR_if_lsigmaleft_equiv_lsigmaright:
equiv[Lsigmaleft.challenge~Lsigmaright.challenge: ={arg} /\  Lsigmaleft.k{1} = Lsigmaright.k{2} ==> ={res} ] => equiv[Lsigma_cpaL.eavesdrop~Lsigma_cpaR.eavesdrop :  ={arg} /\ Lsigma_cpaL.k{1}= Lsigma_cpaR.k{2}==> ={res} ].
    proof.
    progress.
    transitivity Lsigmaleft_eavesdropL.eavesdrop
    (={arg} /\ Lsigma_cpaL.k{1} = Lsigmaleft.k{2} ==> ={res})
    (={arg} /\ Lsigmaleft.k{1} = Lsigma_cpaR.k{2}  ==> ={res}).
    progress.
    exists Lsigma_cpaR.k{2}.
    exists arg{2}.
    auto.
    auto.
    proc.
    inline*.
    simplify.
    wp.
    progress.
    
    (*Transitivity from Lsigmaleft_eavesdropL to Lsigmaright_eavesdropL*)
      transitivity Lsigmaright_eavesdropL.eavesdrop
    ( ={arg} /\ Lsigmaleft.k{1} = Lsigmaright.k{2} ==> ={res})
    ( ={arg} /\ Lsigmaright.k{1} = Lsigma_cpaR.k{2} ==> ={res}).
    progress.
     exists Lsigma_cpaR.k{2}.
      exists arg{2}.
      auto.
      auto.
      proc.
      call H.
      skip.
      auto.

      (*transitivity from Lsigmaright_eavesdropL to Lsigmaright_eavesdropR*)
      transitivity Lsigmaright_eavesdropR.eavesdrop
    (={arg} /\ Lsigmaright.k{1} = Lsigmaright.k{2} ==> ={res})
    (={arg} /\ Lsigmaright.k{1} = Lsigma_cpaR.k{2} ==> ={res}).
      progress.
      exists Lsigma_cpaR.k{2}.
      exists arg{2}.
      auto.
      auto.
      proc.
      inline*.
      auto.

      (*transitivity from Lsigmaright_eavesdropR to Lsigmaleft_eavesdropR*)
      transitivity Lsigmaleft_eavesdropR.eavesdrop
    (={arg} /\ Lsigmaright.k{1} = Lsigmaleft.k{2} ==> ={res})
    (={arg} /\ Lsigmaleft.k{1} = Lsigma_cpaR.k{2} ==> ={res}).
      progress.
      exists Lsigma_cpaR.k{2}.
      exists arg{2}.
      auto.
      auto.
      proc.
      symmetry.
      call H.
      skip.
      progress.

    (*prove Lsigmaleft_eavesdropR_equiv_Lsigma_cpaR*)
      proc.
      inline*.
      wp.
      skip.
      progress.
    qed.

    
