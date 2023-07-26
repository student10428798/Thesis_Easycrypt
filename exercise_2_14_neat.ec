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

module Lsigmaleft    = {
  proc foo(m1:plaintext) : ciphertext = {
  var k:key;
  var c:ciphertext;
  k <$ keygen;
  c <- enc k m1;
  return(c);
    
    }
  }.



      module Lsigmaleft_eavesdropL ={
    proc eavesdrop(m1:plaintext, m2:plaintext) : ciphertext = {
    var c:ciphertext;
    c <@ Lsigmaleft.foo(m1);
      return(c);
      }
    }.


    
module Lsigmaright = {
  proc foo(m1:plaintext) : ciphertext = {
        var m2: plaintext;
  var k:key;
  var c:ciphertext;
        m2 <$ msggen;
  k <$ keygen;
    c <-enc k m2;
    return (c);
    
    }
  }.




  module Lotsl = {
    proc eavesdrop(m1:plaintext,m2:plaintext) : ciphertext = {
      var k:key;
    var c:ciphertext;
    k <$ keygen;
      c <- enc k m1;
      return (c);
    }
  }.

    module LotslHybrid = {
   proc eavesdrop(m1:plaintext,m2:plaintext) : ciphertext = {
   var c:ciphertext;
   c <@ Lsigmaleft.foo(m1);
     return(c);
      }
    }.

    
    


 module Lotsr = {
   proc eavesdrop(m1:plaintext,m2:plaintext) : ciphertext = {
   var k:key;
   var c:ciphertext;
   k <$ keygen;
     c <- enc k m2;
   return(c);
   }
 }.

   module LotsrHybrid ={
   proc eavesdrop(m1:plaintext,m2:plaintext) : ciphertext = {
   var k:key;
     var c:ciphertext;
     var mr;
       mr <- m2;
     c <@ Lsigmaleft.foo(mr);
       return(c);
   }
 }.



   module Lsigmaleft_LotslHybrid ={
    proc foo(m1:plaintext) : ciphertext = {
     var c:ciphertext;
     var m2:plaintext;
     m2 <$ msggen;
    c <@ Lotsl.eavesdrop(m1,m2);
      return(c);
      }
    }.

    module Lsigmaright_LotsrHybrid ={
      proc foo(m1:plaintext) : ciphertext ={
      var c: ciphertext;
      var m2:plaintext;
      m2 <$ msggen;
      c<@ Lotsr.eavesdrop(m1,m2);
      return(c);
        }
      }.
    

       lemma Lsigmaleft_equiv_Lsigmaright_if_one_time_secrecy:
        equiv [Lotsl.eavesdrop~Lotsr.eavesdrop :  ={arg} ==> ={res} ]  =>   equiv[Lsigmaleft.foo~Lsigmaright.foo: ={arg} ==> ={res} ].
           proof.
             progress.
           (*Transitivity from lotsl.eavesdrop to Lsigmaleft_lotslHybrid.foo*)
             transitivity Lsigmaleft_LotslHybrid.foo(={arg} ==> ={res})(={arg} ==> ={res}).
             progress.
             exists arg{2}.
             auto.
             progress.
             proc.
             simplify.
             inline*.
             wp.
             rnd.
             simplify.
             wp.
             progress.
             auto.

           (*transitivity from Lsigmaleft_lotslHybrid.foo to Lsigmaright_lotsrHybrid.foo*)
             transitivity Lsigmaright_LotsrHybrid.foo(={arg} ==> ={res})(={arg} ==> ={res}).
             progress.
             exists arg{2}.
             auto.
             progress.
             proc.
             call H.
             auto.

           
             progress.
           (*Transitivity from Lsigmaright_LotsrHybrid.foo to Lsigmaright *)
             transitivity Lsigmaright_LotsrHybrid.foo(={arg} ==> ={res})(={arg} ==> ={res}).
             progress.
             exists arg{2}.
             auto.
             progress.
             proc.
             inline*.
             wp.
             auto.

           (*Prove that Lsigmaright_LotsrHybrid.foo equivalent Lsigmaright.foo*)
             proc.
             inline*.
             wp.
             auto.
     qed.
 


     (*Rightarrow*)


         (*Lsigmaleft_eavesdropL_equiv_Lsigmaright_eavesdropL*)
      module Lsigmaright_eavesdropL ={
    proc eavesdrop(m1:plaintext, m2:plaintext) : ciphertext = {
    var c:ciphertext;
    c <@ Lsigmaright.foo(m1);
      return(c);
      }
    }.
    

    
    module Lsigmaright_eavesdropR ={
    proc eavesdrop(m1:plaintext, m2:plaintext) : ciphertext = {
    var c:ciphertext;
    c <@ Lsigmaright.foo(m2);
      return(c);
      }
    }.



     module Lsigmaleft_eavesdropR ={
    proc eavesdrop(m1:plaintext, m2:plaintext) : ciphertext = {
    var c:ciphertext;
    c <@ Lsigmaleft.foo(m2);
      return(c);
      }
    }.





        (*The combination of the above proves Lotsl_equiv_lotsr_if_Lsigmaleft_equiv_Lsigmaright*)
    
       lemma one_time_secrecy_if_equivalent_Lsigmaleft_Lsigmaright:
        equiv [Lsigmaleft.foo~Lsigmaright.foo :  ={arg} ==> ={res}] => equiv[Lotsl.eavesdrop~Lotsr.eavesdrop: ={arg} ==> ={res}].
           proof.
             progress.
           (*Transitivity from Lotsl.eavesdrop to Lsigmaleft_eavesdropL.eavesdrop*)
           transitivity Lsigmaleft_eavesdropL.eavesdrop (={arg} ==> ={res})(={arg} ==> ={res}).
             progress.
             exists arg{2}.
             progress.
             trivial.
             proc.
             simplify.
             inline*.
             wp.
             rnd.
             simplify.
             wp.
             skip.
             progress.
           
           (*Transitivity from Lsigmaleft_evaesdropL.eavesdrop to Lsigmaright_eavesdropL.eavesdrop*)
             transitivity Lsigmaright_eavesdropL.eavesdrop(={arg} ==> ={res})(={arg} ==> ={res}).
             progress.
             exists arg{2}.
             auto.
             progress.
             progress.
             proc.
             simplify.
             call H.
             auto.
           
           (*Transitivity from Lsigmaright_eavesdropL.eavesdrop to Lsigmaright_eavesdropR.eavesdrop*)
             transitivity Lsigmaright_eavesdropR.eavesdrop(={arg} ==> ={res})(={arg} ==> ={res}).
             progress.
             exists arg{2}.
             auto.
             progress.
             proc.
             inline*.
             wp.
             rnd.
             auto.
           
           (*Transitivity Lsigmaright_EavesdropR.eavesdrop to Lsigmaleft_eavesdropR.eavesdrop*)
           transitivity Lsigmaleft_eavesdropR.eavesdrop(={arg} ==> ={res})(={arg} ==> ={res}).
             progress.
             exists arg{2}.
             progress.
             auto.
             progress.
             proc.
             simplify.
             symmetry.
             call H.
             auto.

           (*Lsigmaleft_eavesdropR equivalent to lotsr*)
             proc.
             inline*.
             wp.
             rnd.
             simplify.
             auto.
       qed.
