#!/usr/bin/env python3
"""New-output-only build with pre/post header, toolchain and static-library binding."""
import argparse
from pathlib import Path
import shlex
import shutil
import subprocess
from common import Bindings, HERE, require, sha, write_new

def main():
    ap=argparse.ArgumentParser();ap.add_argument('output',type=Path);args=ap.parse_args()
    out=args.output.resolve();obj=Path(str(out)+'.o');pre=Path(str(out)+'.prebuild.json');record=Path(str(out)+'.build.json')
    require(all(not p.exists() for p in (out,obj,pre,record)), 'refusing existing build output/attempt')
    out.parent.mkdir(parents=True,exist_ok=True)
    root=HERE.parents[2];source=HERE/'free_model_solver.c'
    gcc=Path(shutil.which('gcc')).resolve();gxx=Path(shutil.which('g++')).resolve()
    flags=['-O2','-DABC_USE_STDINT_H=1','-DABC_USE_PTHREADS','-I',str(root/'src')]
    depcmd=[str(gcc),*flags,'-M',str(source)]
    dependencies=subprocess.check_output(depcmd,text=True).replace('\\\n',' ')
    headers=[Path(v).resolve() for v in shlex.split(dependencies.split(':',1)[1])]
    bound=Bindings()
    for path in [source,HERE/'build_solver.py',HERE/'build_solver.sh',root/'libabc.a',gcc,gxx,*headers]:bound.add(path)
    tools={}
    for name in ('cc1','as','collect2','ld'):
        value=subprocess.check_output([str(gcc),f'-print-prog-name={name}'],text=True).strip()
        path=Path(value) if '/' in value else Path(shutil.which(value))
        path=path.resolve();bound.add(path);tools[name]=str(path)
    commands=[[str(gcc),*flags,'-c',str(source),'-o',str(obj)],
              [str(gxx),'-o',str(out),str(obj),str(root/'libabc.a'),'-lm','-ldl','-lpthread']]
    versions={str(c):subprocess.check_output([str(c),'--version'],text=True) for c in (gcc,gxx)}
    write_new(pre,dict(schema=1,files=bound.files,commands=commands,dependency_command=depcmd,
                       dependency_output=dependencies,compiler_versions=versions,tools=tools))
    for command in commands:
        bound.check();subprocess.run(command,check=True);bound.check()
    for path in (out,obj,pre):bound.add(path)
    write_new(record,dict(schema=2,solver_sha256=sha(out),source_sha256=sha(source),files=bound.files,
        prebuild_sha256=sha(pre),commands=commands,compiler_versions=versions,tools=tools,
        conflicts_per_query=1000,projection_phase='free',existing_abc_unchanged=True))
if __name__=='__main__':main()
