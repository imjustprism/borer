// Times Ghidra's decompiler for scripts/run/vs_ghidra.py.
//
// Arguments: <out.tsv> <count> where count is how many functions to
// decompile, spread evenly over the program (0 for every function). The
// first line records when the script started (epoch ms), which is when the
// import and auto-analysis finished; each row after is one function:
// entry, milliseconds, and whether the decompile completed.
//@category borer

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;

import ghidra.app.decompiler.DecompInterface;
import ghidra.app.decompiler.DecompileResults;
import ghidra.app.script.GhidraScript;
import ghidra.program.model.listing.Function;

public class BenchDecompile extends GhidraScript {
    @Override
    public void run() throws Exception {
        long started = System.currentTimeMillis();
        String[] args = getScriptArgs();
        Path out = Path.of(args[0]);
        int count = Integer.parseInt(args[1]);

        List<Function> functions = new ArrayList<>();
        for (Function f : currentProgram.getFunctionManager().getFunctions(true)) {
            if (!f.isExternal() && !f.isThunk()) {
                functions.add(f);
            }
        }
        int total = functions.size();
        int want = count <= 0 ? total : Math.min(count, total);
        double step = want == 0 ? 1 : (double) total / want;

        StringBuilder sb = new StringBuilder();
        sb.append("started\t").append(started).append('\n');
        sb.append("functions\t").append(total).append('\n');

        DecompInterface decompiler = new DecompInterface();
        long open0 = System.nanoTime();
        decompiler.openProgram(currentProgram);
        sb.append("open_ms\t").append((System.nanoTime() - open0) / 1e6).append('\n');
        for (int i = 0; i < want; i++) {
            Function f = functions.get((int) (i * step));
            long t0 = System.nanoTime();
            DecompileResults r = decompiler.decompileFunction(f, 60, monitor);
            double ms = (System.nanoTime() - t0) / 1e6;
            sb.append(f.getEntryPoint()).append('\t').append(ms).append('\t')
                .append(r.decompileCompleted()).append('\n');
        }
        decompiler.dispose();
        Files.writeString(out, sb.toString());
    }
}
