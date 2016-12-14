package edu.ucla.cs.process;

import com.google.common.collect.HashMultiset;

import edu.ucla.cs.model.Method;
import edu.ucla.cs.model.MethodCall;

public class ArgumentProcessor extends ProcessStrategy{

	@Override
	void process(String line) {
		Method m = getMethodInstance(line);
		buildArgumentMap(m, line);
	}

	protected void buildArgumentMap(Method m, String line) {
		String s = line.substring(line.indexOf("] =") + 3).trim();
		String[] ss = s.split("@@");
		for(int i = 0; i < ss.length; i++){
			String name = ss[i].split("->")[0];
			String calls = ss[i].split("->")[1];
			
			HashMultiset<MethodCall> mcs = HashMultiset.create();
			
			String[] arr = calls.split(";;;");
			for(int j = 0; j < arr.length; j++) {
				String args = arr[j];
				MethodCall mc = new MethodCall(name, args);
				mcs.add(mc);
			}
			
			m.calls.put(name, mcs);
		}
	}
}
