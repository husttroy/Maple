package edu.ucla.cs.evaluate.top5;

import java.util.ArrayList;
import java.util.HashSet;

import edu.ucla.cs.check.APIMisuseDetection;
import edu.ucla.cs.model.APICall;
import edu.ucla.cs.model.APISeqItem;
import edu.ucla.cs.model.ControlConstruct;

public class MacDoFinal {
	public static void main(String[] args) {
		ArrayList<APISeqItem> pattern1 = new ArrayList<APISeqItem>();
		pattern1.add(new APICall("getBytes", "true", 0));
		pattern1.add(new APICall("doFinal", "true", 1));
		
		ArrayList<APISeqItem> pattern3 = new ArrayList<APISeqItem>();
		pattern3.add(new APICall("getBytes", "true", 1));
		pattern3.add(new APICall("doFinal", "true", 1));
			
		HashSet<ArrayList<APISeqItem>> patterns1 = new HashSet<ArrayList<APISeqItem>>();
		patterns1.add(pattern1);
		
		ArrayList<APISeqItem> pattern2 = new ArrayList<APISeqItem>();
		pattern2.add(ControlConstruct.TRY);
		pattern2.add(new APICall("doFinal", "true", 1));
		pattern2.add(ControlConstruct.END_BLOCK);
		pattern2.add(ControlConstruct.CATCH);
		pattern2.add(ControlConstruct.END_BLOCK);
			
		HashSet<ArrayList<APISeqItem>> patterns2 = new HashSet<ArrayList<APISeqItem>>();
		patterns2.add(pattern2);

		HashSet<HashSet<ArrayList<APISeqItem>>> pset = new HashSet<HashSet<ArrayList<APISeqItem>>>();
		pset.add(patterns1);
		pset.add(patterns2);
		
		HashSet<String> types = new HashSet<String>();
		types.add("String");
		types.add("Mac");
		HashSet<ArrayList<String>> queries = new HashSet<ArrayList<String>>();
		ArrayList<String> apis1 = new ArrayList<String>();
		apis1.add("getBytes(0)");
		apis1.add("doFinal(1)");
		ArrayList<String> apis2 = new ArrayList<String>();
		apis2.add("getBytes(1)");
		apis2.add("doFinal(1)");
		queries.add(apis1);
		queries.add(apis2);
		
		APIMisuseDetection detect = new APIMisuseDetection(types, queries, patterns1);
		detect.run2(pset);
	}
}
