(* Copyright (c) 2015 The Qeditas developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

(**
 White 2015: Moved these to a separate file used by mgcheck.ml, egalqedtheory.ml and egalqeddoc.ml.
 Due to some changes in how polymorphic definitions are handled, some of the hashes changed.
 **)

(*** These are hardcoded axioms. If one were using Egal with different axioms these would need to be changed. ***)
let initializeknowns indexknowns polyexpand =
  if polyexpand then
    begin (*** These are the same as Egal as it was used in the 2014 treasure hunt. ***)
      Hashtbl.add indexknowns "MHJxpbCcvgf6GfLq1S7saPBwmErPKnueV4YrQiNHSDxBodjo" (); (*** prop_ext ***)
      Hashtbl.add indexknowns "MLnnVh41jSSxqd5XHAN5dLiTbnRhXcmdR9JqS8nefceMbXFK" (); (*** func_ext ***)
      Hashtbl.add indexknowns "MKJiK3WGs4Yjw2xCfxtKQmx3caGXoszcAByvYyUWdJmhuqDz" (); (*** EpsR ***)
      Hashtbl.add indexknowns "MMC57kP9yew5kYW425cDP4aDwGpcw4xEQ8a2h4MKVTqTJB2t" (); (*** set_ext ***)
      Hashtbl.add indexknowns "MK3U6ggBH7nVwSfYfTa9HE88hoYeHy3YYdQC4KfYfJmLaUht" (); (*** In_ind ***)
      Hashtbl.add indexknowns "MJxh1BoFqWgt66eB13bFJ4VFnu1TnZEsntngcnLLrQZuyshw" (); (*** EmptyAx ***)
      Hashtbl.add indexknowns "MMDG61WADitW5tC3CGKQaX324Piw6oLtvscga66pNunpQ4CU" (); (*** UnionEq ***)
      Hashtbl.add indexknowns "MMF9Q14pgEVsPXugDeNxDFybtDEGbjAnvY57CM2z74V8eLdF" (); (*** PowerEq ***)
      Hashtbl.add indexknowns "MFtZwsW8bGkPXLyc7MMHxwWu31QCZ6vCZTxPog3HkRrxsLxo" (); (*** ReplEq ***)
      Hashtbl.add indexknowns "MGjf1oAiMpmx2YsyFFHrmGb1t1fbQcyYYb2Px3FfWBeP5uM2" (); (*** UnivOf_In ***)
      Hashtbl.add indexknowns "MK3GRd526Ys1VdSByze4vN96ncHTrh2DwD8J4V8prAgSCev5" (); (*** UnivOf_TransSet ***)
      Hashtbl.add indexknowns "MKLBg12KtP9dLwDfuK7iJ8NCz9jqyCiUUXjqYXotKVuarCW9" (); (*** UnivOf_ZF_closed ***)
      Hashtbl.add indexknowns "MH3Y4r4vcgMQQx8HcpgoMFUuvXz4YURH3ns3hTjF7suFpiUa" (); (*** UnivOf_Min ***)
    end
  else
    begin (*** Some of these are different since some polymorphic definitions (e.g., eq and ex) are no longer expanded before computing the id. ***)
      Hashtbl.add indexknowns "ML2a1Ff4koijntmkbd1Ga5cVC9bnQ81dfu575Ly75jo3ubuM" (); (*** prop_ext ***)
      Hashtbl.add indexknowns "MLnnVh41jSSxqd5XHAN5dLiTbnRhXcmdR9JqS8nefceMbXFK" (); (*** func_ext ***)
      Hashtbl.add indexknowns "MKJiK3WGs4Yjw2xCfxtKQmx3caGXoszcAByvYyUWdJmhuqDz" (); (*** EpsR ***)
      Hashtbl.add indexknowns "MKecr6dpqvxUWVU1kCqi6nExzAehfvaiZGcrcT7jFWBtn9tP" (); (*** set_ext ***)
      Hashtbl.add indexknowns "MK3U6ggBH7nVwSfYfTa9HE88hoYeHy3YYdQC4KfYfJmLaUht" (); (*** In_ind ***)
      Hashtbl.add indexknowns "MJ6TuZYktNnirGe8mu9M7W3gXR7CsEZiMa8PCqC3MgVyqv7f" (); (*** EmptyAx ***)
      Hashtbl.add indexknowns "MK3LtMzCbaGdnzYrK4Q2QdELC21m8VREEoFbT7CmuUwtAVwy" (); (*** UnionEq ***)
      Hashtbl.add indexknowns "MMF9Q14pgEVsPXugDeNxDFybtDEGbjAnvY57CM2z74V8eLdF" (); (*** PowerEq ***)
      Hashtbl.add indexknowns "MGDd3XnNWK4rCrkT5mBV5BVqDUP95VArWBq9gr3Bk32NFCFu" (); (*** ReplEq ***)
      Hashtbl.add indexknowns "MGjf1oAiMpmx2YsyFFHrmGb1t1fbQcyYYb2Px3FfWBeP5uM2" (); (*** UnivOf_In ***)
      Hashtbl.add indexknowns "MK3GRd526Ys1VdSByze4vN96ncHTrh2DwD8J4V8prAgSCev5" (); (*** UnivOf_TransSet ***)
      Hashtbl.add indexknowns "MKLBg12KtP9dLwDfuK7iJ8NCz9jqyCiUUXjqYXotKVuarCW9" (); (*** UnivOf_ZF_closed ***)
      Hashtbl.add indexknowns "MH3Y4r4vcgMQQx8HcpgoMFUuvXz4YURH3ns3hTjF7suFpiUa" () (*** UnivOf_Min ***)
    end
