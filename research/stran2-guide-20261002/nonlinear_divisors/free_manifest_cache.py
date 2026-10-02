"""Opt-in immutable free-manifest IO cache; never a proof/domain authority.

Every version is first authenticated against its existing exact reference.
Per-witness replay remains in free_guided. Chunk entry/exit, checkpoint and final
boundaries still perform full hashes. All source/proof identities stay external.
"""
from collections import Counter, OrderedDict
from contextlib import contextmanager
from dataclasses import dataclass
import hashlib
import json
import os
from pathlib import Path
import stat
from types import MappingProxyType

RUNTIME=['nonlinear_divisors/free_manifest_cache.py']
POLICY='immutable_free_manifest_cache_v1'

def require(condition,message):
    if not condition:raise ValueError(message)
def freeze(value):
    if isinstance(value,dict):return MappingProxyType({k:freeze(v)for k,v in value.items()})
    if isinstance(value,list):return tuple(freeze(v)for v in value)
    return value
def plain(value):
    if isinstance(value,dict)or isinstance(value,MappingProxyType):return {k:plain(v)for k,v in value.items()}
    if isinstance(value,(tuple,list)):return [plain(v)for v in value]
    return value
def anchor(s):return s.st_dev,s.st_ino,s.st_size,s.st_mtime_ns,s.st_ctime_ns
def directory_anchor(path):
    s=path.lstat();require(stat.S_ISDIR(s.st_mode),'manifest directory is not an ordinary directory')
    return s.st_dev,s.st_ino
def guarded(method):
    def invoke(self,*args,**kwargs):
        try:
            require(not self.closed,'manifest cache is closed')
            return method(self,*args,**kwargs)
        except BaseException:
            self.close();raise
    return invoke

@dataclass(frozen=True)
class Identity:
    reference: tuple
    key: tuple
    path: Path
    anchor: tuple

class ManifestCache:
    MAX_ENTRIES=2
    def __init__(self,case_out,input_sha256,dimensions,deadline):
        case=Path(case_out).absolute()
        require(case.resolve()==case,'manifest case path is not canonical')
        self.case,self.directory=case,case/'free_domains'
        self.case_anchor=directory_anchor(case);self.directory_anchor=directory_anchor(self.directory)
        self.input_sha256=input_sha256;self.ni,self.nl=dimensions;self.deadline=deadline
        self.identities={};self.entries=OrderedDict();self.metrics=Counter();self.closed=False
        self.implementation_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()

    def _reference(self,bound):
        require(isinstance(bound,dict),'invalid manifest reference')
        require(set(bound)=={'file','sha256','free_version','free_domain_sha256','free_signature_bits'},'manifest reference fields differ')
        name=bound['file'];version=bound['free_version'];lanes=bound['free_signature_bits']
        require(type(version)is int and 0<=version<=256 and name==f'version_{version:05d}.json','invalid manifest version/path')
        require(type(lanes)is int and 256<=lanes<=512,'invalid manifest lane count')
        for key in ('sha256','free_domain_sha256'):
            require(type(bound[key])is str and len(bound[key])==64 and all(c in '0123456789abcdef'for c in bound[key]),'invalid manifest hash')
        return tuple(sorted(bound.items()))

    def _parents(self):
        require(self.case.resolve()==self.case and self.directory.resolve()==self.directory,'manifest path now contains a symlink')
        require(directory_anchor(self.case)==self.case_anchor and directory_anchor(self.directory)==self.directory_anchor,
                'manifest directory identity changed')

    def _check(self,identity,fd=None):
        self.deadline.remaining();self._parents();s=identity.path.lstat()
        require(stat.S_ISREG(s.st_mode) and anchor(s)==identity.anchor,'manifest anchored identity changed')
        if fd is not None:require(anchor(os.fstat(fd))==identity.anchor,'open manifest identity changed')
        self.metrics['identity_checks']+=1

    def _evict(self):
        for version,entry in list(self.entries.items()):
            if not entry['borrowed']:
                self.entries.pop(version);os.close(entry['fd']);self.metrics['descriptor_closes']+=1
                self.metrics['evictions']+=1;return
        raise ValueError('all manifest cache descriptors are borrowed')

    def _open(self,identity):
        self._check(identity)
        while len(self.entries)>=self.MAX_ENTRIES:self._evict()
        fd=os.open(identity.path,os.O_RDONLY|os.O_CLOEXEC|os.O_NOFOLLOW)
        entry=dict(fd=fd,payload=None,borrowed=0)
        self.entries[dict(identity.reference)['free_version']]=entry
        self.metrics['descriptor_opens']+=1
        self.metrics['peak_open_descriptors']=max(self.metrics['peak_open_descriptors'],len(self.entries))
        self._check(identity,fd);return entry

    def _read(self,identity,entry,parse):
        self._check(identity,entry['fd']);os.lseek(entry['fd'],0,os.SEEK_SET)
        digest=hashlib.sha256();parts=[]
        while True:
            self.deadline.remaining();block=os.read(entry['fd'],1024*1024)
            if not block:break
            digest.update(block);self.metrics['full_hash_bytes']+=len(block)
            if parse:parts.append(block)
        self._check(identity,entry['fd'])
        require(digest.hexdigest()==dict(identity.reference)['sha256'],'manifest full content hash changed')
        self.metrics['full_hash_checks']+=1
        if parse:
            payload=json.loads(b''.join(parts));self._validate(identity,payload)
            entry['payload']=freeze(payload);self.metrics['payload_parses']+=1
        self.deadline.remaining()

    def _validate(self,identity,payload):
        bound=dict(identity.reference)
        require(payload['schema']==1 and payload['input_sha256']==self.input_sha256 and
                payload['domain']=='unrestricted_free_PI_RO' and payload['free_version']==bound['free_version'] and
                payload['free_domain_sha256']==bound['free_domain_sha256'] and
                payload['free_signature_bits']==bound['free_signature_bits'],'manifest payload key differs')
        require(payload['initial_lanes']==256 and payload['global_added_cap']==256 and
                payload['sampled_pi_field']=='previous_inputs' and
                int(payload['free_mask'],16)==(1<<bound['free_signature_bits'])-1,'manifest domain/frame differs')
        require(len(payload['initial_ci_signatures'])==self.ni+self.nl and
                all(type(v)is str and 0<=int(v,16)<1<<256 for v in payload['initial_ci_signatures']),
                'manifest initial lane dimensions differ')
        records=payload['records'];require(len(records)==bound['free_signature_bits']-256,'incomplete manifest lane records')
        for i,row in enumerate(records):
            require(row['lane']==256+i and row['domain']=='unrestricted_free_PI_RO' and
                    row['sampled_pi_field']=='previous_inputs','manifest lane order/frame differs')
            require(len(row['inputs'])==self.ni and len(row['state'])==self.nl and
                    all(type(v)is int and v in (0,1)for v in row['inputs']+row['state']),'manifest world is incomplete/non-Boolean')
            require(json.loads(row['provenance_json'])['input_sha256']==self.input_sha256,'manifest origin input differs')
        require(identity.key==(self.input_sha256,bound['free_version'],bound['free_domain_sha256'],bound['sha256'],
                              payload['initial_domain_sha256'],bound['free_signature_bits'],str(self.case)),
                'manifest complete cache key differs')

    def _identity(self,bound):
        reference=self._reference(bound);version=bound['free_version']
        require(version in self.identities,'unregistered manifest version')
        identity=self.identities[version]
        require(identity.reference==reference,'manifest same-version reference changed')
        return identity

    def _entry(self,identity):
        version=dict(identity.reference)['free_version'];entry=self.entries.get(version)
        if entry is None:
            entry=self._open(identity);self._read(identity,entry,parse=True);self.metrics['reloads']+=1
        else:self._check(identity,entry['fd']);self.entries.move_to_end(version)
        return entry

    @guarded
    def check_creation_destination(self,name):
        self.deadline.remaining();self._parents()
        require(type(name)is str and name.startswith('version_') and name.endswith('.json') and
                name[8:-5].isdigit() and Path(name).name==name,'invalid manifest creation name')
        for path in (self.directory/name,(self.directory/name).with_suffix('.json.tmp')):
            require(not path.exists() and not path.is_symlink(),'manifest creation destination already exists')

    @guarded
    def write_new(self,name,payload):
        """Linux anchored-dir publication without replacing any existing file.

        The final hard link targets the open exclusive temp descriptor, not a
        mutable temp pathname. Publication fails if the final name already exists.
        Evict read handles first so the directory+writer descriptors also fit2.
        """
        self.check_creation_destination(name)
        while self.entries:self._evict()
        directory_fd=temp_fd=None;temp=name+'.tmp';created=False
        try:
            directory_fd=os.open(self.directory,os.O_RDONLY|os.O_DIRECTORY|os.O_CLOEXEC|os.O_NOFOLLOW)
            self.metrics['descriptor_opens']+=1
            self.metrics['peak_open_descriptors']=max(self.metrics['peak_open_descriptors'],1)
            require((os.fstat(directory_fd).st_dev,os.fstat(directory_fd).st_ino)==self.directory_anchor,
                    'creation directory descriptor identity changed')
            self._parents()
            temp_fd=os.open(temp,os.O_WRONLY|os.O_CREAT|os.O_EXCL|os.O_CLOEXEC|os.O_NOFOLLOW,0o666,dir_fd=directory_fd)
            created=True;self.metrics['descriptor_opens']+=1
            self.metrics['peak_open_descriptors']=max(self.metrics['peak_open_descriptors'],2)
            data=(json.dumps(payload,indent=2,sort_keys=True)+'\n').encode()
            view=memoryview(data)
            while view:
                self.deadline.remaining();count=os.write(temp_fd,view)
                require(count>0,'manifest write made no progress');view=view[count:]
            self._parents();self.deadline.remaining()
            saved=os.fstat(temp_fd);named=os.stat(temp,dir_fd=directory_fd,follow_symlinks=False)
            require(stat.S_ISREG(named.st_mode) and anchor(named)==anchor(saved),'exclusive temp identity changed')
            os.link(f'/proc/self/fd/{temp_fd}',name,dst_dir_fd=directory_fd,follow_symlinks=True)
            final=os.stat(name,dir_fd=directory_fd,follow_symlinks=False)
            require(stat.S_ISREG(final.st_mode) and anchor(final)==anchor(os.fstat(temp_fd)),
                    'published manifest identity differs from open writer')
            named=os.stat(temp,dir_fd=directory_fd,follow_symlinks=False)
            require(stat.S_ISREG(named.st_mode) and anchor(named)==anchor(os.fstat(temp_fd)),
                    'exclusive temp identity changed during publication')
            self._parents();self.deadline.remaining();self.metrics['manifest_publications']+=1
        finally:
            try:
                if created and directory_fd is not None and temp_fd is not None:
                    try:
                        current=os.stat(temp,dir_fd=directory_fd,follow_symlinks=False);opened=os.fstat(temp_fd)
                        if (current.st_dev,current.st_ino)==(opened.st_dev,opened.st_ino):os.unlink(temp,dir_fd=directory_fd)
                    except FileNotFoundError:pass
            finally:
                for fd in (temp_fd,directory_fd):
                    if fd is not None:
                        try:os.close(fd)
                        except OSError:pass
                        self.metrics['descriptor_closes']+=1

    @guarded
    def register(self,bound,expected_payload):
        """Authenticate one creation, or a separately bound saved-record fixture.

        expected_payload comes from the immutable writer snapshot. The saved
        record harness must bind its old evidence separately; no job is rewritten.
        """
        self.deadline.remaining();reference=self._reference(bound);version=bound['free_version']
        require(version not in self.identities,'manifest version already registered')
        self._parents();path=self.directory/bound['file'];s=path.lstat()
        require(stat.S_ISREG(s.st_mode),'manifest is not an ordinary file')
        key=(self.input_sha256,version,bound['free_domain_sha256'],bound['sha256'],
             expected_payload['initial_domain_sha256'],bound['free_signature_bits'],str(self.case))
        identity=Identity(reference,key,path,anchor(s));self.identities[version]=identity
        entry=self._open(identity);self._read(identity,entry,parse=True)
        require(plain(entry['payload'])==plain(expected_payload),'manifest differs from immutable writer payload')
        self.metrics['registered_versions']+=1
        self.deadline.remaining()

    @guarded
    def check_identity(self,bound):
        identity=self._identity(bound);entry=self.entries.get(bound['free_version'])
        self._check(identity,entry['fd']if entry else None)

    @guarded
    def authenticate(self,bounds):
        seen=set()
        for bound in bounds:
            identity=self._identity(bound)
            if identity.key in seen:continue
            seen.add(identity.key);entry=self._entry(identity)
            self._read(identity,entry,parse=False)
        self.deadline.remaining()

    @contextmanager
    def witness_payload(self,bound):
        try:
            require(not self.closed,'manifest cache is closed')
            identity=self._identity(bound);entry=self._entry(identity);entry['borrowed']+=1
            try:
                self._check(identity,entry['fd']);yield entry['payload'];self._check(identity,entry['fd'])
            finally:entry['borrowed']-=1
        except BaseException:
            self.close();raise

    @contextmanager
    def identity_boundary(self,bound):
        try:
            self.check_identity(bound);yield;self.check_identity(bound)
        except BaseException:
            self.close();raise

    @contextmanager
    def proof_boundary(self,candidates):
        try:
            bounds=[c['free_domain']['manifest']for c in candidates]
            self.authenticate(bounds);yield;self.authenticate(bounds)
        except BaseException:
            self.close();raise

    @guarded
    def verify_all(self):
        self.authenticate([dict(m.reference)for m in self.identities.values()])

    def report(self):
        return dict(policy=POLICY,implementation_sha256=self.implementation_sha256,
                    cache_capacity=self.MAX_ENTRIES,registered_versions=len(self.identities),
                    open_descriptors=len(self.entries),closed=self.closed,metrics=dict(self.metrics))

    def close(self):
        for entry in self.entries.values():
            try:os.close(entry['fd'])
            except OSError:pass
            self.metrics['descriptor_closes']+=1
        self.entries.clear();self.closed=True
