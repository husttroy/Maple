package edu.ucla.cs.process;

import edu.ucla.cs.model.Method;

public class SequenceProcessor extends ProcessStrategy {

	@Override
	void process(String line) {
		Method m = getMethodInstance(line);
		buildSequenceMap(m, line);
	}
	
	protected void buildSequenceMap(Method method, String line) {
		String s = line.substring(line.indexOf("] =") + 3).trim();
		String[] ss = s.split("->");
		// skip the first element because it is empty string
		for(int i = 1; i < ss.length; i++){
			if(ss[i].contains("}")){
				String api = ss[i].split("}")[0];
				method.seq.add(api);
				method.seq.add("}");
			}else{
				method.seq.add(ss[i].trim());
			}
		}
	}
}
