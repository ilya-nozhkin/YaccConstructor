﻿using System;
using System.Linq;
using Highlighting.Gen;
using Highlighting.Tree;
using JetBrains.Application.Settings;
using JetBrains.ReSharper.Daemon;
using JetBrains.ReSharper.Daemon.Stages;
using JetBrains.ReSharper.Psi;
using JetBrains.ReSharper.Psi.Tree;

namespace Highlighting.CodeInspections
{
    public abstract class MyDaemonStageProcessBase : TreeNodeVisitor<IHighlightingConsumer>, IRecursiveElementProcessor<IHighlightingConsumer>, IDaemonStageProcess
    {
        public IDaemonProcess myDaemonProcess;
        public IFile myFile;

        public IContextBoundSettingsStore mySettingsStore;

        protected MyDaemonStageProcessBase(IDaemonProcess process, IContextBoundSettingsStore settingsStore)
        {
            myDaemonProcess = process;
            myFile = MyDaemonStageBase.GetPsiFile(myDaemonProcess.SourceFile);
            mySettingsStore = settingsStore;
        }
        
        public IFile File
        {
            get { return myFile; }
        }

        #region IDaemonStageProcess Members

        public IDaemonProcess DaemonProcess
        {
          get { return myDaemonProcess; }
        }

        public abstract void Execute(Action<DaemonStageResult> commiter);

        #endregion

        #region IRecursiveElementProcessor<IHighlightingConsumer> Members

        public virtual bool InteriorShouldBeProcessed(ITreeNode element, IHighlightingConsumer context)
        {
            return true;
        }

        public bool IsProcessingFinished(IHighlightingConsumer context)
        {
            return false;
        }


        public virtual void ProcessBeforeInterior(ITreeNode element, IHighlightingConsumer consumer)
        {
        }

        public virtual void ProcessAfterInterior(ITreeNode element, IHighlightingConsumer consumer)
        {
            var myElement = element as IAbstractTreeNode; 
            if (myElement != null)
            {
                //VisitSomething(element, consumer);
                myElement.Accept(this, consumer);
            }
            //else
            //{
            //    //VisitNode(element, consumer);
            //}
        }

        #endregion

        protected void HighlightInFile(Action<IFile, IHighlightingConsumer> fileHighlighter, Action<DaemonStageResult> commiter)
        {
            var consumer = new DefaultHighlightingConsumer(this, mySettingsStore);
            fileHighlighter(File, consumer);
            commiter(new DaemonStageResult(consumer.Highlightings));
        }
    }
}
