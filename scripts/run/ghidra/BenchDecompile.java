// Times Ghidra's decompiler for scripts/run/vs_ghidra.py.
//
// Arguments: <out.tsv> <count> [parallel]. The first line records when the
// script started (epoch ms), which is when the import and auto-analysis
// finished. With a count above 0 the script decompiles the first function
// (the `first` line, timed from when the script started, so it includes
// starting the decompiler), then `count` functions spread evenly over the
// program, the first one left out. With a count of 0 it decompiles every
// function, one at a time with one decompiler, or with `parallel` through
// Ghidra's ParallelDecompiler, the one its C exporter uses, on every core.
// Every decompile runs with the program's decompiler options, as the GUI
// does, and a 60 s timeout. Each row after is one function: entry,
// milliseconds, and whether the decompile completed; `all_ms` is the wall
// time of the whole sweep and `failed` how many did not complete.
//@category borer

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.atomic.AtomicInteger;

import ghidra.app.decompiler.DecompInterface;
import ghidra.app.decompiler.DecompileOptions;
import ghidra.app.decompiler.DecompileResults;
import ghidra.app.decompiler.parallel.DecompilerCallback;
import ghidra.app.decompiler.parallel.ParallelDecompiler;
import ghidra.app.script.GhidraScript;
import ghidra.program.model.listing.Function;
import ghidra.program.model.listing.Program;
import ghidra.util.task.TaskMonitor;

public class BenchDecompile extends GhidraScript {
    private static final int TIMEOUT_S = 60;

    private static void configure(DecompInterface d, Program program) {
        DecompileOptions options = new DecompileOptions();
        options.grabFromProgram(program);
        d.setOptions(options);
    }

    @Override
    public void run() throws Exception {
        long started = System.currentTimeMillis();
        String[] args = getScriptArgs();
        Path out = Path.of(args[0]);
        int count = Integer.parseInt(args[1]);
        boolean parallel = args.length > 2 && args[2].equals("parallel");

        List<Function> functions = new ArrayList<>();
        for (Function f : currentProgram.getFunctionManager().getFunctions(true)) {
            if (!f.isExternal() && !f.isThunk()) {
                functions.add(f);
            }
        }
        int total = functions.size();
        StringBuilder sb = new StringBuilder();
        sb.append("started\t").append(started).append('\n');
        sb.append("functions\t").append(total).append('\n');
        sb.append("cores\t").append(Runtime.getRuntime().availableProcessors()).append('\n');

        if (parallel) {
            AtomicInteger failed = new AtomicInteger();
            DecompilerCallback<Boolean> callback =
                new DecompilerCallback<>(currentProgram, d -> configure(d, currentProgram)) {
                    @Override
                    public Boolean process(DecompileResults r, TaskMonitor m) {
                        if (!r.decompileCompleted()) {
                            failed.incrementAndGet();
                        }
                        return r.decompileCompleted();
                    }
                };
            callback.setTimeout(TIMEOUT_S);
            long t0 = System.nanoTime();
            ParallelDecompiler.decompileFunctions(callback, functions, monitor);
            sb.append("all_ms\t").append((System.nanoTime() - t0) / 1e6).append('\n');
            sb.append("failed\t").append(failed.get()).append('\n');
            callback.dispose();
            Files.writeString(out, sb.toString());
            return;
        }

        DecompInterface decompiler = new DecompInterface();
        configure(decompiler, currentProgram);
        decompiler.openProgram(currentProgram);
        List<Function> picked = new ArrayList<>();
        if (count <= 0) {
            picked = functions;
        } else if (total > 0) {
            DecompileResults r = decompiler.decompileFunction(functions.get(0), TIMEOUT_S, monitor);
            sb.append("first\t").append(System.currentTimeMillis() - started).append('\t')
                .append(r.decompileCompleted()).append('\n');
            int want = Math.min(count, total - 1);
            double step = (double) (total - 1) / Math.max(want, 1);
            for (int i = 0; i < want; i++) {
                picked.add(functions.get(1 + (int) (i * step)));
            }
        }
        int failed = 0;
        long all0 = System.nanoTime();
        for (Function f : picked) {
            long t0 = System.nanoTime();
            DecompileResults r = decompiler.decompileFunction(f, TIMEOUT_S, monitor);
            double ms = (System.nanoTime() - t0) / 1e6;
            if (!r.decompileCompleted()) {
                failed++;
            }
            sb.append(f.getEntryPoint()).append('\t').append(ms).append('\t')
                .append(r.decompileCompleted()).append('\n');
        }
        sb.append("all_ms\t").append((System.nanoTime() - all0) / 1e6).append('\n');
        sb.append("failed\t").append(failed).append('\n');
        decompiler.dispose();
        Files.writeString(out, sb.toString());
    }
}
