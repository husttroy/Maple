package edu.ucla.cs.evaluate.human;

import java.util.ArrayList;
import java.util.HashSet;

import edu.ucla.cs.check.APIMisuseDetection;
import edu.ucla.cs.model.APICall;
import edu.ucla.cs.model.APISeqItem;
import edu.ucla.cs.model.ControlConstruct;

public class InputStream {
	public static void main(String[] args) {
		ArrayList<APISeqItem> pattern1 = new ArrayList<APISeqItem>();
		pattern1.add(new APICall("read", "true", 1));
		pattern1.add(new APICall("close", "true", 0));
		
		HashSet<ArrayList<APISeqItem>> patterns1 = new HashSet<ArrayList<APISeqItem>>();
		patterns1.add(pattern1);
		
		ArrayList<APISeqItem> pattern2 = new ArrayList<APISeqItem>();
		pattern2.add(ControlConstruct.TRY);
		pattern2.add(new APICall("read", "true", 1));
		pattern2.add(ControlConstruct.END_BLOCK);
		
		HashSet<ArrayList<APISeqItem>> patterns2 = new HashSet<ArrayList<APISeqItem>>();
		patterns2.add(pattern2);
		
		HashSet<HashSet<ArrayList<APISeqItem>>> pset = new HashSet<HashSet<ArrayList<APISeqItem>>>();
		pset.add(patterns1);
		pset.add(patterns2);
		
		HashSet<String> types = new HashSet<String>();
		types.add("InputStream");
		HashSet<ArrayList<String>> queries = new HashSet<ArrayList<String>>();
		ArrayList<String> apis = new ArrayList<String>();
		apis.add("read(1)");
		queries.add(apis);
		
		APIMisuseDetection detect = new APIMisuseDetection(types, queries, patterns1);
		detect.run2(pset);
	}
}
